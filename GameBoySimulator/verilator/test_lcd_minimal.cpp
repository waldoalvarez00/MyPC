// Minimal LCD test without SDRAM
#include <verilated.h>
#include "Vtop.h"
#include <stdio.h>

void tick(Vtop* dut) {
    dut->clk_sys = 1;
    dut->eval();
    dut->clk_sys = 0;
    dut->eval();
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Minimal LCD Test (No SDRAM) ===\n");

    printf("Creating DUT...\n");
    Vtop* dut = new Vtop;

    printf("Initializing signals...\n");
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

    printf("Running reset cycles...\n");
    for (int i = 0; i < 100; i++) {
        tick(dut);
    }

    dut->reset = 0;

    printf("Running 1000 cycles...\n");
    for (int i = 0; i < 1000; i++) {
        tick(dut);
    }

    printf("\nChecking signals:\n");
    printf("  dbg_ce_cpu: %d\n", dut->dbg_ce_cpu);
    printf("  dbg_lcd_mode: %d\n", dut->dbg_lcd_mode);
    printf("  dbg_isGBC_game: %d\n", dut->dbg_isGBC_game);
    printf("  dbg_lcd_data_gb: %d\n", dut->dbg_lcd_data_gb);
    printf("  dbg_lcd_data: 0x%04X\n", dut->dbg_lcd_data);
    printf("  VGA_R: %d\n", dut->VGA_R);
    printf("  VGA_G: %d\n", dut->VGA_G);
    printf("  VGA_B: %d\n", dut->VGA_B);

    printf("\nCleaning up...\n");
    delete dut;

    printf("=== Test Complete ===\n");
    return 0;
}
