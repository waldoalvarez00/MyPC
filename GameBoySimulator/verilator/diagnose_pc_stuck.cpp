#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== PC Stuck Diagnostic ===\n\n");

    // Load a simple test ROM
    uint8_t rom[32768];
    memset(rom, 0x00, sizeof(rom));

    // Add RETI at interrupt vectors
    rom[0x40] = 0xD9;  // VBlank: RETI
    rom[0x48] = 0xD9;  // LCD STAT: RETI
    rom[0x50] = 0xD9;  // Timer: RETI
    rom[0x58] = 0xD9;  // Serial: RETI
    rom[0x60] = 0xD9;  // Joypad: RETI

    // Entry point
    rom[0x100] = 0x00;  // NOP
    rom[0x101] = 0xC3;  // JP $0150
    rom[0x102] = 0x50;
    rom[0x103] = 0x01;

    // Nintendo logo (CRITICAL for boot ROM logo verification)
    uint8_t logo[] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
    };
    memcpy(&rom[0x104], logo, sizeof(logo));

    // Main program at 0x150
    int pc = 0x150;
    rom[pc++] = 0xF3;  // DI (disable interrupts)
    rom[pc++] = 0x31; rom[pc++] = 0xFE; rom[pc++] = 0xFF;  // LD SP, $FFFE
    rom[pc++] = 0x00;  // NOP
    rom[pc++] = 0x18; rom[pc++] = 0xFD;  // JR -3 (infinite loop)

    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    // Simulate cart download
    printf("Simulating cart download...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;

    for (int i = 0; i < 10; i++) {
        dut->ioctl_addr = i;
        dut->ioctl_wr = 1;

        for (int j = 0; j < 64; j++) {
            tick_with_sdram(dut, sdram);
        }

        dut->ioctl_wr = 0;

        for (int j = 0; j < 64; j++) {
            tick_with_sdram(dut, sdram);
        }

        if (dut->dbg_cart_ready) {
            printf("  cart_ready set after %d writes\n", i + 1);
            break;
        }
    }

    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;

    printf("Cart download complete, cart_ready=%d\n\n", dut->dbg_cart_ready);

    if (!dut->dbg_cart_ready) {
        printf("ERROR: cart_ready NOT SET!\n");
        printf("This means cart ROM won't respond to reads.\n");
        printf("Boot ROM logo verification will fail.\n\n");
    }

    // Run simulation and watch for PC getting stuck
    printf("Monitoring PC for stuck condition...\n\n");

    uint16_t last_pc = 0xFFFF;
    int same_pc_count = 0;
    int pc_history[10] = {0};
    int hist_idx = 0;

    for (int cycle = 0; cycle < 50000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint16_t sp = dut->dbg_cpu_sp;

        // Track PC history
        pc_history[hist_idx] = pc;
        hist_idx = (hist_idx + 1) % 10;

        // Detect PC stuck
        if (pc == last_pc) {
            same_pc_count++;

            if (same_pc_count == 100) {
                printf("Cycle %d: PC STUCK DETECTED!\n", cycle);
                printf("  PC stuck at: 0x%04X\n", pc);
                printf("  SP: 0x%04X\n", sp);
                printf("  boot_rom_enabled: %d\n", dut->dbg_boot_rom_enabled);
                printf("  cart_ready: %d\n", dut->dbg_cart_ready);
                printf("  ce_cpu: %d\n", dut->dbg_ce_cpu);

                printf("\n  PC History (last 10 samples):\n");
                for (int i = 0; i < 10; i++) {
                    int idx = (hist_idx + i) % 10;
                    printf("    [%d] 0x%04X\n", i, pc_history[idx]);
                }

                // Check what's at this address
                if (dut->dbg_boot_rom_enabled && pc < 0x100) {
                    printf("\n  PC is in BOOT ROM range (0x%04X < 0x0100)\n", pc);
                    printf("  Boot ROM might be stuck in a loop\n");
                    printf("  Possible causes:\n");
                    printf("    - Logo verification failing\n");
                    printf("    - Delay loop not completing\n");
                    printf("    - cart_ready not set (cart ROM not responding)\n");
                } else if (!dut->dbg_boot_rom_enabled && pc < 0x0100) {
                    printf("\n  PC in low memory but boot ROM disabled!\n");
                    printf("  This is CART ROM area but might be blank\n");
                } else {
                    printf("\n  PC at 0x%04X\n", pc);
                }

                // Check cart ROM at this address
                printf("\n  Cart ROM content at PC:\n");
                for (int i = 0; i < 8; i++) {
                    printf("    [0x%04X] = 0x%02X\n", pc + i, sdram->read8(pc + i));
                }

                break;
            }
        } else {
            same_pc_count = 0;
        }

        // Check for address range that indicates problems
        if ((pc >= 0x0038 && pc <= 0x0042) || (pc >= 0x0048 && pc <= 0x0062)) {
            printf("Cycle %d: PC IN INTERRUPT VECTOR RANGE!\n", cycle);
            printf("  PC: 0x%04X\n", pc);
            printf("  SP: 0x%04X (was 0x%04X)\n", sp, last_pc);
            printf("  This suggests interrupt storm!\n");

            if (same_pc_count > 5) {
                printf("  PC stuck in interrupt range - breaking\n");
                break;
            }
        }

        last_pc = pc;

        // Progress indicator
        if (cycle % 10000 == 0 && cycle > 0) {
            printf("Cycle %d: PC=0x%04X SP=0x%04X boot_en=%d\n",
                   cycle, pc, sp, dut->dbg_boot_rom_enabled);
        }
    }

    printf("\n--- Final State ---\n");
    printf("PC: 0x%04X\n", dut->dbg_cpu_addr);
    printf("SP: 0x%04X\n", dut->dbg_cpu_sp);
    printf("boot_rom_enabled: %d\n", dut->dbg_boot_rom_enabled);
    printf("cart_ready: %d\n", dut->dbg_cart_ready);

    delete sdram;
    delete dut;
    return 0;
}
