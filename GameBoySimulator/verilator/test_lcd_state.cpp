// Test to check LCD state and timing
#include <verilated.h>
#include "Vtop.h"
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== LCD State Test ===\n");

    Vtop* dut = new Vtop();

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;

    // Run some cycles with reset
    for (int i = 0; i < 100; i++) {
        dut->clk_sys = 0;
        dut->eval();
        dut->clk_sys = 1;
        dut->eval();
    }

    // Release reset
    dut->reset = 0;
    printf("Reset released\n\n");

    // Monitor LCD state over time
    int total_cycles = 0;
    
    for (int i = 0; i < 100000; i++) {
        dut->clk_sys = 0;
        dut->eval();
        dut->clk_sys = 1;
        dut->eval();
        total_cycles++;
        
        if (i % 10000 == 0) {
            printf("Cycle %d:\n", total_cycles);
            printf("  LCDC: 0x%02X (LCD ON: %d)\n", dut->dbg_lcdc, (dut->dbg_lcdc >> 7) & 1);
            printf("  lcd_on: %d\n", dut->dbg_lcd_on);
            printf("  lcd_clkena: %d\n", dut->dbg_lcd_clkena);
            printf("  lcd_mode: %d\n", dut->dbg_lcd_mode);
            printf("  video_ly: %d\n", dut->dbg_video_ly);
            printf("  ce_cpu: %d\n", dut->dbg_ce_cpu);
            printf("  cpu_clken: %d\n", dut->dbg_cpu_clken);
            printf("\n");
        }
    }
    
    delete dut;
    return 0;
}
