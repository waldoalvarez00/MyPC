#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== CPU Timing vs SDRAM Data Ready ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Write data
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_addr = 0x0104;
    dut->ioctl_dout = 0xEDCE;
    dut->ioctl_wr = 1;
    tick_with_sdram(dut, sdram);
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    for (int i = 0; i < 50; i++) tick_with_sdram(dut, sdram);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("Watching for when ce_cpu pulses vs when sdram_do has data:\n\n");
    printf("Cycle | ce_cpu | ce_cpu2x | cart_rd | sdram_do | cpu_di |\n");
    printf("------|--------|----------|---------|----------|--------|\n");

    bool found = false;
    int count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool ce_cpu = dut->dbg_ce_cpu;
        bool ce_cpu2x = dut->dbg_sdram_sync;  // This is ce_cpu2x
        bool cart_rd = dut->dbg_cart_rd;
        uint16_t sdram_do = dut->dbg_sdram_do;
        uint8_t cpu_di = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && cart_rd) {
            if (count < 50) {
                printf("%5d | %6d | %8d | %7d | 0x%04X   | 0x%02X   |",
                       cycle, ce_cpu, ce_cpu2x, cart_rd, sdram_do, cpu_di);

                if (ce_cpu) printf(" ← CPU SAMPLES HERE!");
                if (sdram_do == 0xEDCE) printf(" ← DATA READY");

                printf("\n");
                count++;
            }
            found = true;
        }

        tick_with_sdram(dut, sdram);
        if (found && count >= 50) break;
    }

    printf("\n--- Analysis ---\n");
    printf("The CPU samples data when ce_cpu=1.\n");
    printf("If sdram_do doesn't have data when ce_cpu=1, CPU gets zeros.\n");
    printf("Solution: Either stall CPU until data ready, or ensure data\n");
    printf("arrives before the ce_cpu pulse.\n");

    delete sdram;
    delete dut;
    return 0;
}
