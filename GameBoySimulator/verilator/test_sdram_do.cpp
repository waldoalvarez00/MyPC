#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== SDRAM Data Path Trace ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Write data
    printf("Step 1: Write $EDCE to SDRAM[0x0104]\n");
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

    printf("  SDRAM memory[0x104] = 0x%02X\n\n", sdram->memory[0x104]);

    printf("Step 2: Trace data through SDRAM controller to CPU\n\n");
    printf("Cycle | dout_r | sdram_do | cpu_di | Note\n");
    printf("------|--------|----------|--------|------\n");

    bool found = false;
    int count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        uint16_t dout_r = dut->dbg_sdram_dout_r;
        uint16_t sdram_do = dut->dbg_sdram_do;
        uint8_t cpu_di = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && (dout_r != 0 || sdram_do != 0 || cpu_di != 0)) {
            if (count < 40) {
                printf("%5d | 0x%04X | 0x%04X   | 0x%02X   |",
                       cycle, dout_r, sdram_do, cpu_di);

                if (dout_r == 0xEDCE) printf(" dout_r OK!");
                if (sdram_do == 0xEDCE) printf(" sdram_do OK!");
                if (cpu_di == 0xCE) printf(" CPU GOT IT!");

                printf("\n");
                count++;
            }
            found = true;
        }

        tick_with_sdram(dut, sdram);
        if (found && count >= 40) break;
    }

    printf("\n--- Analysis ---\n");
    printf("Data should flow: SDRAM memory → dout_r → sdram_do → CPU\n");

    delete sdram;
    delete dut;
    return 0;
}
