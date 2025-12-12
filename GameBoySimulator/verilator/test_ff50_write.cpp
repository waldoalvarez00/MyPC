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

    printf("=== Monitoring $FF50 Write ===\n\n");

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

    printf("Monitoring for writes to $FF50...\n\n");

    bool found_ff50_write = false;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t cpu_clken = dut->dbg_cpu_clken;
        uint8_t wr_n_edge = dut->dbg_cpu_wr_n_edge;
        uint8_t old_wr_n = dut->dbg_old_cpu_wr_n;

        // Check for any access to $FF50
        if (addr == 0xFF50) {
            printf("  [%6d] CPU accessing $FF50: wr_n=%d old_wr_n=%d edge=%d clken=%d\n",
                   i, wr_n, old_wr_n, wr_n_edge, cpu_clken);

            if (wr_n == 0) {
                printf("             *** WRITE to $FF50 detected! ***\n");
                found_ff50_write = true;

                // Monitor for several cycles to see edge
                for (int j = 0; j < 10; j++) {
                    tick_with_sdram(dut, sdram);
                    printf("  [%6d] wr_n=%d old_wr_n=%d edge=%d clken=%d boot_enabled=%d\n",
                           i+j+1, dut->dbg_cpu_wr_n, dut->dbg_old_cpu_wr_n,
                           dut->dbg_cpu_wr_n_edge, dut->dbg_cpu_clken,
                           dut->dbg_boot_rom_enabled ? 1 : 0);
                }
                break;
            }
        }

        // Stop after cart entry
        if (dut->dbg_cpu_pc >= 0x0102) {
            printf("\n  Reached cart entry without seeing $FF50 write\n");
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("Found $FF50 write: %s\n", found_ff50_write ? "YES" : "NO");
    printf("Boot ROM enabled: %s\n", dut->dbg_boot_rom_enabled ? "YES" : "NO");

    if (found_ff50_write && dut->dbg_boot_rom_enabled) {
        printf("\n✗ BUG: $FF50 write occurred but boot ROM still enabled\n");
        printf("  Possible causes:\n");
        printf("  - Clock enable (ce/clken) not true during write\n");
        printf("  - Edge detector not triggering\n");
        printf("  - Boot ROM disable logic not executing\n");
    } else if (!found_ff50_write) {
        printf("\n⚠ CPU never wrote to $FF50\n");
    } else {
        printf("\n✓ Boot ROM disabled successfully\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
