#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== JR Instruction PC Transition Analysis ===\n\n");
    printf("Capturing detailed state around each PC transition\n\n");

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

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // Fill with HALT

    // At 0x100: JP to 0x150
    rom[0x100] = 0xC3;  // JP $0150
    rom[0x101] = 0x50;
    rom[0x102] = 0x01;

    // At 0x150: JP to 0x160 (working instruction)
    rom[0x150] = 0xC3;  // JP $0160
    rom[0x151] = 0x60;
    rom[0x152] = 0x01;

    // At 0x160: JR +2 (failing instruction)
    rom[0x160] = 0x18;  // JR +2
    rom[0x161] = 0x02;  // Offset
    rom[0x162] = 0x76;  // HALT (should skip)
    rom[0x163] = 0x00;  // NOP (target)
    rom[0x164] = 0x76;  // HALT

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

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;
    int pc_change_count = 0;
    int global_cycle = 0;

    bool reached_jp_at_150 = false;
    bool reached_jr_at_160 = false;
    int jp_transitions = 0;
    int jr_transitions = 0;

    printf("Running simulation...\n\n");

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);
        global_cycle++;

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot completed at cycle %d\n\n", cycle);
            printf("--- Cart ROM PC Transitions ---\n");
            printf("Cycle   PC     Data  Opcode      cpu_clken ce_cpu cart_rd cpu_rd_n\n");
            printf("-----   ----   ----  ----------  --------- ------ ------- --------\n");
        }

        // Track PC changes after boot
        if (boot_completed && pc != last_pc) {
            pc_change_count++;

            // Get opcode name for readability
            const char* opcode_name = "?";
            uint8_t opcode = (pc < sizeof(rom)) ? rom[pc] : 0xFF;

            if (pc == 0x100 && opcode == 0xC3) opcode_name = "JP $0150";
            else if (pc == 0x101) opcode_name = "JP addr low";
            else if (pc == 0x102) opcode_name = "JP addr high";
            else if (pc == 0x150 && opcode == 0xC3) opcode_name = "JP $0160";
            else if (pc == 0x151) opcode_name = "JP addr low";
            else if (pc == 0x152) opcode_name = "JP addr high";
            else if (pc == 0x160 && opcode == 0x18) opcode_name = "JR +2";
            else if (pc == 0x161) opcode_name = "JR offset";
            else if (pc == 0x162 && opcode == 0x76) opcode_name = "HALT ← BUG!";
            else if (pc == 0x163) opcode_name = "NOP (target)";
            else if (opcode == 0x00) opcode_name = "NOP";
            else if (opcode == 0x76) opcode_name = "HALT";

            // Print PC transition with signals
            printf("%5d  $%04X   $%02X  %-12s    %d        %d       %d        %d\n",
                   cycle, pc, opcode, opcode_name,
                   dut->dbg_cpu_clken, dut->dbg_ce_cpu, dut->dbg_cart_rd, dut->dbg_cpu_rd_n);

            // Track JP instruction progression (0x150-0x15F)
            if (pc >= 0x150 && pc < 0x160) {
                if (!reached_jp_at_150 && pc == 0x150) {
                    reached_jp_at_150 = true;
                    printf("\n>>> JP Instruction Started at $0150 <<<\n\n");
                }
                jp_transitions++;
            }

            // Track JR instruction progression (0x160-0x165)
            if (pc >= 0x160 && pc <= 0x165) {
                if (!reached_jr_at_160 && pc == 0x160) {
                    reached_jr_at_160 = true;
                    printf("\n>>> JR Instruction Started at $0160 <<<\n\n");
                }
                jr_transitions++;
            }

            // Stop if we hit HALT at 0x162 (JR failed)
            if (pc == 0x162) {
                printf("\n❌ JR FAILED: Hit HALT at 0x162!\n");
                printf("   PC progressed: $0160 → $0161 → $0162 (byte-by-byte)\n");
                printf("   Expected: $0160 → $0163 (jump)\n\n");
                break;
            }

            // Success if we reach 0x163
            if (pc == 0x163) {
                printf("\n✅ JR SUCCESS: Reached target at 0x163!\n");
                printf("   PC correctly jumped: $0160 → $0163\n\n");
                break;
            }

            // Stop after 50 PC changes to keep output readable
            if (pc_change_count >= 50) {
                printf("\n(Stopped after 50 PC transitions)\n");
                break;
            }

            last_pc = pc;
        }
    }

    // Analysis
    printf("\n=== Analysis ===\n\n");
    printf("JP Instruction (0x150-0x15F):\n");
    printf("  PC transitions: %d\n", jp_transitions);
    printf("  Status: %s\n", (jp_transitions >= 3) ? "✅ EXECUTED" : "❌ STUCK");
    printf("\n");

    printf("JR Instruction (0x160-0x165):\n");
    printf("  PC transitions: %d\n", jr_transitions);
    if (last_pc == 0x162) {
        printf("  Status: ❌ FAILED - Hit HALT (PC incremented byte-by-byte)\n");
        printf("  Conclusion: JR instruction not executing jump\n");
    } else if (last_pc == 0x163) {
        printf("  Status: ✅ SUCCESS - Reached target\n");
    } else {
        printf("  Status: ❓ UNKNOWN - PC=%04X\n", last_pc);
    }

    delete sdram;
    delete dut;

    return (last_pc == 0x162) ? 1 : 0;  // Return error if hit HALT
}
