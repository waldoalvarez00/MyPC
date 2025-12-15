// Test to check if LY (scanline counter) increments
#include <verilated.h>
#include "Vtop.h"
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== LY Counter Test ===\n");

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
    printf("Reset released\n");

    // Monitor LY value over time
    int prev_ly = -1;
    int ly_changes = 0;
    int total_cycles = 0;
    
    for (int frame = 0; frame < 3; frame++) {  // Run for ~3 frames
        for (int i = 0; i < 100000; i++) {
            dut->clk_sys = 0;
            dut->eval();
            dut->clk_sys = 1;
            dut->eval();
            total_cycles++;
            
            int ly = dut->dbg_video_ly;
            if (ly != prev_ly) {
                if (ly_changes < 30 || ly == 0 || ly == 144) {
                    printf("Cycle %d: LY changed from %d to %d\n", total_cycles, prev_ly, ly);
                }
                prev_ly = ly;
                ly_changes++;
            }
        }
    }

    printf("\nTotal LY changes: %d\n", ly_changes);
    printf("Final LY: %d\n", dut->dbg_video_ly);
    
    delete dut;
    return 0;
}
