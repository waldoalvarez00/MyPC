#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    // MisterSDRAMModel ctor takes size in MB (not bytes).
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Detailed PC Trace ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM
    dut->boot_download = 1;
    for (int i = 0; i < 256; i += 2) {
        dut->boot_addr = i;
        dut->boot_data = boot_rom[i] | (boot_rom[i+1] << 8);
        dut->boot_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;

    // Simulate cart
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Showing PC trace (every PC change for first 500 changes):\n\n");

    uint16_t last_pc = 0xFFFF;
    int pc_changes = 0;

    for (int i = 0; i < 200000 && pc_changes < 500; i++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;

        if (pc != last_pc) {
            pc_changes++;

            // Show every 10th PC change to keep output manageable
            if (pc_changes % 10 == 0 || pc_changes <= 50 || pc >= 0x0100) {
                printf("  [%6d] #%4d: PC=$%04X", i, pc_changes, pc);

                if (pc >= 0x0100) {
                    printf(" *** BEYOND BOOT ROM ***");
                }

                if (!dut->dbg_boot_rom_enabled) {
                    printf(" (boot ROM disabled)");
                }

                printf("\n");
            }

            last_pc = pc;
        }

        // Stop if boot ROM disabled
        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  Boot ROM disabled at cycle %d, PC=$%04X\n", i, pc);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("PC changes: %d\n", pc_changes);
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);
    printf("Boot ROM enabled: %s\n", dut->dbg_boot_rom_enabled ? "YES" : "NO");

    delete sdram;
    delete dut;
    return 0;
}
