#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Checking if CPU gets stuck at $000B ===\n\n");

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

    printf("Running until PC reaches $000B, then monitoring for 10000 more cycles...\n\n");

    int reached_000b = -1;
    uint16_t last_pc = 0;

    for (int i = 0; i < 50000; i++) {
        uint16_t pc = dut->dbg_cpu_pc;

        // Detect when we first reach $000B
        if (pc == 0x000B && reached_000b < 0) {
            reached_000b = i;
            printf("  [%6d] First reached PC=$000B\n", i);
            printf("  Monitoring for next 10000 cycles to see if PC advances...\n\n");
        }

        // After reaching $000B, monitor for any PC changes
        if (reached_000b >= 0 && i < reached_000b + 10000) {
            if (pc != last_pc) {
                printf("  [%6d] PC=$%04X (moved from $%04X after %d cycles)\n",
                       i, pc, last_pc, i - reached_000b);

                if (pc >= 0x000C) {
                    printf("\n  *** PC advanced beyond $000B! Boot ROM continuing... ***\n\n");

                    // Show next few PC changes
                    for (int j = 0; j < 50; j++) {
                        uint16_t old_pc = dut->dbg_cpu_pc;
                        tick_with_sdram(dut, sdram);
                        if (dut->dbg_cpu_pc != old_pc) {
                            printf("  [%6d] PC=$%04X\n", i+j, dut->dbg_cpu_pc);
                        }
                    }
                    break;
                }
            }
        }

        last_pc = pc;
        tick_with_sdram(dut, sdram);

        if (reached_000b >= 0 && i >= reached_000b + 10000) {
            printf("\n  [%6d] 10000 cycles elapsed, PC still at $%04X\n", i, pc);
            printf("  *** CPU STUCK AT $000B ***\n");
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);

    if (dut->dbg_cpu_pc == 0x000B) {
        printf("\n✗ BUG: CPU stuck at $000B (LD A, $80 instruction)\n");
        printf("  This suggests the instruction is not completing\n");
    } else if (dut->dbg_cpu_pc > 0x000B) {
        printf("\n✓ CPU progressed past $000B\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
