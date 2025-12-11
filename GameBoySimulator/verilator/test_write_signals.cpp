#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Write Signals Test ===\n\n");

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

    printf("Looking for write to $FF40 and checking ALL relevant signals...\n\n");

    for (int i = 0; i < 15000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;

        tick_with_sdram(dut, sdram);

        // Look for any access to $FF40
        if (addr == 0xFF40) {
            uint8_t data = dut->dbg_cpu_do;
            uint8_t lcdc = dut->dbg_lcdc;
            
            printf("  [%6d] Access to $FF40: wr_n=%d edge=%d data=$%02X lcdc=$%02X\n",
                   i, wr_n, wr_edge, data, lcdc);
            
            if (wr_edge == 0 && wr_n == 0) {
                printf("           *** WRITE DETECTED ***\n");
                
                // Check 10 more cycles
                for (int j = 1; j <= 10; j++) {
                    tick_with_sdram(dut, sdram);
                    printf("           [+%d] lcdc=$%02X\n", j, dut->dbg_lcdc);
                }
                
                printf("\n  Analysis:\n");
                printf("    - Write to $FF40 with data=$91\n");
                printf("    - But LCDC register = $%02X (should be $91!)\n", dut->dbg_lcdc);
                printf("    - This means the always block is NOT executing the write\n");
                printf("\n  Possible causes:\n");
                printf("    1. cpu_sel_reg signal is not true for $FF40\n");
                printf("    2. cpu_wr signal timing issue\n");
                printf("    3. Reset or savestate overriding the write\n");
                printf("    4. negedge clk timing issue\n");
                
                break;
            }
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
