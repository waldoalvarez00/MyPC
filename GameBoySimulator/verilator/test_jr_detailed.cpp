#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== JR Instruction Detailed Analysis ===\n\n");

    // Minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;  // NOP
    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[pc++] = 0x50;

    // Test ROM with JP then JR
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // Fill with HALT

    rom[0x100] = 0xC3;  // JP $0150
    rom[0x101] = 0x50;
    rom[0x102] = 0x01;

    // At 0x150: JP to 0x160 (known working)
    rom[0x150] = 0xC3;  // JP $0160
    rom[0x151] = 0x60;
    rom[0x152] = 0x01;

    // At 0x160: JR +2 (skip one byte to 0x163)
    rom[0x160] = 0x18;  // JR +2
    rom[0x161] = 0x02;  // Offset = +2
    rom[0x162] = 0x76;  // HALT (should skip)
    rom[0x163] = 0x00;  // NOP (target)
    rom[0x164] = 0x76;  // HALT

    printf("Test Configuration:\n");
    printf("  0x0150: JP $0160 (verifies JP works)\n");
    printf("  0x0160: JR +2 (should jump to 0x0163)\n");
    printf("  0x0162: HALT (should skip)\n");
    printf("  0x0163: NOP (target)\n\n");

    // Load into SDRAM
    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    // Upload boot ROM
    printf("Uploading boot ROM...\n");
    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t word = minimal_boot[addr];
        if (addr + 1 < 256) word |= (minimal_boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;

    // Simulate cart download
    printf("Simulating cart download...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    for (int i = 0; i < 10; i++) {
        dut->ioctl_addr = i;
        dut->ioctl_wr = 1;
        run_cycles_with_sdram(dut, sdram, 64);
        dut->ioctl_wr = 0;
        run_cycles_with_sdram(dut, sdram, 64);
        if (dut->dbg_cart_ready) break;
    }
    dut->ioctl_download = 0;
    printf("Ready\n\n");

    // Run with detailed logging
    printf("Running simulation...\n\n");

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;
    int cart_pc_changes = 0;
    bool reached_0x160 = false;
    bool jr_executed = false;
    int cycles_at_160 = 0;
    int cycles_at_161 = 0;
    int cycles_at_162 = 0;
    int cycles_at_163 = 0;

    for (int cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot completed at cycle %d\n\n", cycle);
            printf("--- Cart ROM Execution ---\n");
        }

        // Track PC changes in cart ROM
        if (boot_completed && pc != last_pc) {
            cart_pc_changes++;

            // Print all PC changes until we understand the issue
            if (cart_pc_changes <= 50) {
                printf("  [%2d] PC=$%04X", cart_pc_changes, pc);

                if (pc >= 0x100 && pc < 0x200) {
                    printf(" (byte=0x%02X", rom[pc]);
                    if (pc == 0x160) printf(" = JR opcode");
                    else if (pc == 0x161) printf(" = JR offset");
                    else if (pc == 0x162) printf(" = HALT ← BUG");
                    else if (pc == 0x163) printf(" = NOP ← target");
                    printf(")");
                }

                // Show debug signals for addresses near JR
                if (pc >= 0x15F && pc <= 0x165) {
                    printf(" [cpu_clken=%d ce_cpu=%d cart_rd=%d]",
                           dut->dbg_cpu_clken, dut->dbg_ce_cpu, dut->dbg_cart_rd);
                }

                printf("\n");
            }

            // Count cycles at each address
            if (pc == 0x160) { cycles_at_160++; reached_0x160 = true; }
            if (pc == 0x161) cycles_at_161++;
            if (pc == 0x162) cycles_at_162++;
            if (pc == 0x163) { cycles_at_163++; jr_executed = true; }

            // Stop if we hit HALT at 0x162
            if (pc == 0x162) {
                printf("\n❌ JR FAILED: Hit HALT at 0x0162!\n");
                printf("   Cycle breakdown:\n");
                printf("     0x0160 (JR opcode): %d PC changes\n", cycles_at_160);
                printf("     0x0161 (JR offset): %d PC changes\n", cycles_at_161);
                printf("     0x0162 (HALT): %d PC changes ← Should be 0!\n", cycles_at_162);
                printf("     0x0163 (target): %d PC changes\n\n", cycles_at_163);
                break;
            }

            // Stop if we successfully reach target at 0x163
            if (pc == 0x163) {
                printf("\n✅ JR WORKED: Reached target at 0x0163!\n");
                printf("   Cycle breakdown:\n");
                printf("     0x0160 (JR opcode): %d PC changes\n", cycles_at_160);
                printf("     0x0161 (JR offset): %d PC changes\n", cycles_at_161);
                printf("     0x0162 (HALT): %d PC changes ← Correct (skipped)\n", cycles_at_162);
                printf("     0x0163 (target): %d PC changes\n\n", cycles_at_163);
                break;
            }

            last_pc = pc;
        }
    }

    printf("\n=== Analysis ===\n");
    printf("Reached 0x0160 (JR instruction): %s\n", reached_0x160 ? "YES" : "NO");
    printf("JR executed successfully: %s\n", jr_executed ? "YES" : "NO");

    if (reached_0x160 && !jr_executed) {
        printf("\n⚠️  CONCLUSION: JR instruction does NOT execute!\n");
        printf("   PC increments byte-by-byte instead of jumping.\n");
        printf("   This is a CPU core or wait state timing issue.\n\n");

        printf("Hypothesis:\n");
        printf("   1. TV80 core may have bug with JR in GameBoy mode\n");
        printf("   2. Wait state logic may not trigger correctly for 2-byte instructions\n");
        printf("   3. JR offset calculation may be incorrect\n\n");

        printf("Next steps:\n");
        printf("   1. Check if real game ROM uses JR instructions\n");
        printf("   2. Test with zero CAS latency (cas_latency=0)\n");
        printf("   3. Examine TV80 core JR implementation\n");
    }

    delete sdram;
    delete dut;

    return jr_executed ? 0 : 1;
}
