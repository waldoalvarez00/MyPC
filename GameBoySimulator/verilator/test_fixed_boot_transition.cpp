#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Fixed Boot ROM Transition Test ===\n\n");

    // Create FIXED minimal boot ROM (matches sim_main_gui.cpp fix)
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);

    int pc = 0;

    // 0. Disable interrupts
    minimal_boot[pc++] = 0xF3;  // DI

    // 1. Turn off LCD
    minimal_boot[pc++] = 0x3E;  // LD A, $00
    minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF40), A
    minimal_boot[pc++] = 0x40;

    // 2. FIXED TRANSITION: Load target into HL, disable boot ROM, jump via register
    minimal_boot[pc++] = 0x21;  // LD HL, $0100
    minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[pc++] = 0x50;
    minimal_boot[pc++] = 0xE9;  // JP (HL)  <-- FIXED!

    printf("Fixed boot ROM created: %d bytes\n", pc);
    printf("  Boot ROM transition fix: APPLIED\n");
    printf("  Method: JP (HL) instead of JP $0100\n\n");

    // Create cart ROM
    uint8_t rom[32768];
    memset(rom, 0xFF, sizeof(rom));  // Fill with 0xFF to detect wild jumps

    // Add RETI at interrupt vectors
    rom[0x40] = 0xD9;
    rom[0x48] = 0xD9;
    rom[0x50] = 0xD9;
    rom[0x58] = 0xD9;
    rom[0x60] = 0xD9;

    // Entry point
    rom[0x100] = 0x00;  // NOP
    rom[0x101] = 0xC3;  // JP $0150
    rom[0x102] = 0x50;
    rom[0x103] = 0x01;

    // Nintendo logo
    uint8_t logo[] = {0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B};
    memcpy(&rom[0x104], logo, sizeof(logo));

    // Main program at 0x150
    pc = 0x150;
    rom[pc++] = 0xF3;  // DI
    rom[pc++] = 0x31; rom[pc++] = 0xFE; rom[pc++] = 0xFF;  // LD SP, $FFFE
    rom[pc++] = 0x00;  // NOP
    rom[pc++] = 0x18; rom[pc++] = 0xFD;  // JR -3

    printf("Cart ROM created\n\n");

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
    printf("Uploading fixed boot ROM...\n");
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
    printf("Boot ROM uploaded\n\n");

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
        if (dut->dbg_cart_ready) {
            printf("  cart_ready set\n");
            break;
        }
    }
    dut->ioctl_download = 0;
    printf("Cart download complete\n\n");

    // Run simulation
    printf("Running simulation with fixed boot ROM transition...\n\n");

    bool boot_completed = false;
    int boot_complete_cycle = -1;
    bool reached_0x0100 = false;
    int reached_0x0100_cycle = -1;
    bool reached_0x0150 = false;
    int reached_0x0150_cycle = -1;
    bool jumped_to_high_memory = false;
    bool stuck_at_0x0038 = false;
    int stuck_count = 0;
    uint16_t last_pc = 0xFFFF;

    for (int cycle = 0; cycle < 10000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot ROM completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            boot_complete_cycle = cycle;
            printf("Cycle %d: ✅ Boot ROM completed and disabled\n", cycle);
            printf("  PC at completion: 0x%04X\n", pc);
        }

        // Detect reaching cart entry point 0x0100
        if (!reached_0x0100 && pc == 0x0100) {
            reached_0x0100 = true;
            reached_0x0100_cycle = cycle;
            printf("Cycle %d: ✅ Reached cart entry point (0x0100)\n", cycle);
        }

        // Detect reaching main program 0x0150
        if (!reached_0x0150 && pc == 0x0150) {
            reached_0x0150 = true;
            reached_0x0150_cycle = cycle;
            printf("Cycle %d: ✅ Reached main program (0x0150)\n", cycle);
        }

        // Detect wild jump to high memory (0xFFF0-0xFFFF)
        if (pc >= 0xFFF0 && pc <= 0xFFFF) {
            jumped_to_high_memory = true;
            printf("Cycle %d: ❌ PC in high memory (0x%04X) - TRANSITION BUG!\n", cycle, pc);
            break;
        }

        // Detect stuck at 0x0038
        if (pc == 0x0038) {
            if (pc == last_pc) {
                stuck_count++;
                if (stuck_count >= 10) {
                    stuck_at_0x0038 = true;
                    printf("Cycle %d: ❌ PC stuck at 0x0038 - INTERRUPT STORM!\n", cycle);
                    break;
                }
            } else {
                stuck_count = 0;
            }
        } else {
            stuck_count = 0;
        }

        last_pc = pc;

        // Stop after reaching main program for 100 cycles
        if (reached_0x0150 && (cycle - reached_0x0150_cycle) > 100) {
            printf("\nCycle %d: ✅ Main program running stably for 100+ cycles\n", cycle);
            break;
        }
    }

    printf("\n--- Test Results ---\n");
    printf("Boot ROM completed: %s (cycle %d)\n",
           boot_completed ? "YES" : "NO", boot_complete_cycle);
    printf("Reached 0x0100: %s (cycle %d)\n",
           reached_0x0100 ? "YES" : "NO", reached_0x0100_cycle);
    printf("Reached 0x0150: %s (cycle %d)\n",
           reached_0x0150 ? "YES" : "NO", reached_0x0150_cycle);
    printf("Jumped to high memory: %s\n", jumped_to_high_memory ? "YES (BUG!)" : "NO");
    printf("Stuck at 0x0038: %s\n", stuck_at_0x0038 ? "YES (BUG!)" : "NO");

    printf("\n");
    if (!jumped_to_high_memory && !stuck_at_0x0038 && reached_0x0150) {
        printf("✅ TEST PASSED!\n");
        printf("   Boot ROM transition fix WORKS\n");
        printf("   No PC corruption, no interrupt storm\n");
    } else {
        printf("❌ TEST FAILED!\n");
        if (jumped_to_high_memory) printf("   PC went to high memory (transition bug)\n");
        if (stuck_at_0x0038) printf("   PC stuck at 0x0038 (interrupt storm)\n");
        if (!reached_0x0150) printf("   Never reached main program\n");
    }

    delete sdram;
    delete dut;
    return (jumped_to_high_memory || stuck_at_0x0038) ? 1 : 0;
}
