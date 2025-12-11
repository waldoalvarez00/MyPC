#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== VRAM Address Increment Test ===\n\n");

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

    printf("Monitoring VRAM write addresses:\n\n");

    int vram_writes = 0;
    uint16_t last_addr = 0;

    for (int i = 0; i < 20000; i++) {
        tick_with_sdram(dut, sdram);

        // Monitor ACTUAL VRAM writes
        if (dut->dbg_vram_wren &&
            dut->dbg_cpu_addr >= 0x8000 &&
            dut->dbg_cpu_addr < 0xA000) {

            vram_writes++;

            if (vram_writes <= 50) {
                printf("  [%6d] VRAM[%04X] write #%d (prev=$%04X, diff=%+d)\n",
                       i, dut->dbg_cpu_addr, vram_writes, last_addr,
                       (int)dut->dbg_cpu_addr - (int)last_addr);
            }

            last_addr = dut->dbg_cpu_addr;

            // Loop should exit at address $8010 (when L=$10, bit 4 = 1)
            if (dut->dbg_cpu_addr >= 0x8010) {
                printf("\n  [%6d] *** Reached $8010 - loop should exit now ***\n", i);

                // Check PC for next 100 cycles
                for (int j = 0; j < 100; j++) {
                    uint16_t pc = dut->dbg_cpu_pc;
                    tick_with_sdram(dut, sdram);
                    if (dut->dbg_cpu_pc != pc) {
                        printf("  [%6d] PC=$%04X\n", i+j, dut->dbg_cpu_pc);
                    }
                }
                break;
            }
        }
    }

    printf("\n--- Results ---\n");
    printf("Total VRAM writes: %d\n", vram_writes);
    printf("Last address: $%04X\n", last_addr);

    if (last_addr < 0x8010) {
        printf("✗ Loop did not progress to $8010\n");
    } else {
        printf("✓ Loop reached $8010\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
