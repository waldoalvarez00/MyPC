// Simple LCD test to debug segfault
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <stdio.h>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Simple LCD Test ===\n");

    printf("Creating DUT...\n");
    Vtop* dut = new Vtop;

    printf("Creating SDRAM model...\n");
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("Resetting DUT...\n");
    reset_dut_with_sdram(dut, sdram, 100);

    printf("Running 1000 cycles...\n");
    run_cycles_with_sdram(dut, sdram, 1000);

    printf("Checking signals:\n");
    printf("  dbg_ce_cpu: %d\n", dut->dbg_ce_cpu);
    printf("  dbg_lcd_mode: %d\n", dut->dbg_lcd_mode);
    printf("  dbg_isGBC_game: %d\n", dut->dbg_isGBC_game);
    printf("  dbg_lcd_data_gb: %d\n", dut->dbg_lcd_data_gb);
    printf("  VGA_R: %d\n", dut->VGA_R);
    printf("  VGA_G: %d\n", dut->VGA_G);
    printf("  VGA_B: %d\n", dut->VGA_B);

    printf("\nCleaning up...\n");
    delete sdram;
    delete dut;

    printf("=== Test Complete ===\n");
    return 0;
}
