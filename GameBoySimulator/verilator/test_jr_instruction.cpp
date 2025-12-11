#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // REALISTIC latency

    printf("=== JR Instruction Execution Test ===\n\n");

    // Create minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);

    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI

    while (pc < 0xFC) {
        minimal_boot[pc++] = 0x00;  // NOP
    }

    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[pc++] = 0x50;

    // Create cart ROM with JR instruction
    uint8_t rom[32768];
    memset(rom, 0x00, sizeof(rom));  // Fill with NOP

    // Entry at 0x100
    rom[0x100] = 0xC3;  // JP $0150
    rom[0x101] = 0x50;
    rom[0x102] = 0x01;

    // Test JR at 0x150
    rom[0x150] = 0x00;  // NOP
    rom[0x151] = 0x18;  // JR +3 (skip to 0x157)
    rom[0x152] = 0x03;  // Offset = +3
    rom[0x153] = 0x76;  // HALT (should skip this)
    rom[0x154] = 0x76;  // HALT (should skip this)
    rom[0x155] = 0x76;  // HALT (should skip this)
    rom[0x156] = 0x76;  // HALT (should skip this)
    rom[0x157] = 0x00;  // NOP (target)
    rom[0x158] = 0x18;  // JR -3 (loop back to 0x157)
    rom[0x159] = 0xFD;  // Offset = -3

    printf("ROM Configuration:\n");
    printf("  0x0100: JP $0150\n");
    printf("  0x0150: NOP\n");
    printf("  0x0151: JR +3 (should jump to 0x0157)\n");
    printf("  0x0153-0x0156: HALT x4 (should be skipped)\n");
    printf("  0x0157: NOP (target)\n");
    printf("  0x0158: JR -3 (should loop to 0x0157)\n\n");

    // Verify ROM bytes
    printf("ROM bytes at 0x150-0x15A:\n  ");
    for (int i = 0; i < 11; i++) {
        printf("%02X ", rom[0x150 + i]);
    }
    printf("\n\n");

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

    // Run and track PC
    printf("Running simulation...\n\n");

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;
    int cart_pc_changes = 0;
    bool reached_0x157 = false;
    int loop_at_0x157 = 0;
    bool hit_halt = false;

    for (int cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot ROM completed at cycle %d, PC=$%04X\n\n", cycle, pc);
            printf("--- Cart ROM Execution Trace ---\n");
        }

        // Track cart ROM execution
        if (boot_completed && pc != last_pc) {
            cart_pc_changes++;

            // Print first 100 PC changes
            if (cart_pc_changes <= 100) {
                printf("  Cart PC[%3d]: $%04X", cart_pc_changes, pc);

                // Show what CPU is executing
                if (pc >= 0x100 && pc < 0x200) {
                    printf(" (ROM[$%04X] = 0x%02X)", pc, rom[pc]);
                }
                printf("\n");
            }

            // Check if reached 0x157 (target of first JR)
            if (pc == 0x157 && !reached_0x157) {
                reached_0x157 = true;
                printf("\n  ✅ SUCCESS: Reached $0157 (first JR executed correctly!)\n\n");
            }

            // Check if hitting HALT at 0x153-0x156
            if (pc >= 0x153 && pc <= 0x156) {
                hit_halt = true;
                printf("\n  ❌ ERROR: Hit HALT at $%04X!\n", pc);
                printf("     JR +3 did NOT jump!\n\n");
                break;
            }

            // Check if looping at 0x157
            if (pc == 0x157) {
                loop_at_0x157++;
                if (loop_at_0x157 == 5) {
                    printf("  ✅ Looping at $0157 (second JR working!)\n\n");
                    break;
                }
            }

            last_pc = pc;
        }
    }

    printf("\n=== Test Result ===\n");
    if (hit_halt) {
        printf("❌ FAIL: JR instruction did NOT execute (forward jump)\n");
        printf("   PC hit HALT instead of jumping to target\n");
    } else if (reached_0x157 && loop_at_0x157 >= 2) {
        printf("✅ PASS: Both JR instructions executed correctly\n");
        printf("   Forward jump (+3): ✅\n");
        printf("   Backward jump (-3): ✅\n");
    } else if (reached_0x157) {
        printf("⚠️  PARTIAL: Forward JR works, but backward JR issue\n");
        printf("   Forward jump (+3): ✅\n");
        printf("   Backward jump (-3): ❌\n");
    } else {
        printf("❌ FAIL: JR instruction completely broken\n");
    }

    delete sdram;
    delete dut;
    return (reached_0x157 && loop_at_0x157 >= 2) ? 0 : 1;
}
