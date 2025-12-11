#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);  // 8 MB
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== SDRAM dout_r Capture Test ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Write data to SDRAM
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

    printf("  SDRAM memory[0x104] = 0x%02X (expect 0xCE)\n\n", sdram->memory[0x104]);

    printf("Step 2: Monitor SDRAM controller internals during cart ROM read\n\n");

    printf("Cycle | State | oe_r | sd_data_in | dout_r | Note\n");
    printf("------|-------|------|------------|--------|------\n");

    bool found_read = false;
    int trace_count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool cart_rd = dut->dbg_cart_rd;
        uint8_t state = dut->dbg_sdram_state;
        bool oe_r = dut->dbg_sdram_oe_r;
        uint16_t sd_data_in = dut->sd_data_in;
        uint16_t dout_r = dut->dbg_sdram_dout_r;

        if (cpu_addr == 0x0104 && (cart_rd || sd_data_in != 0 || dout_r != 0)) {
            if (trace_count < 40) {
                const char* state_name = (state == 0) ? "IDLE" :
                                        (state == 1) ? "ACT " :
                                        (state == 2) ? "READ" :
                                        (state == 3) ? "WR  " :
                                        (state == 4) ? "REF " :
                                        (state == 5) ? "PRE " : "??? ";

                printf("%5d | %s | %4d | 0x%04X     | 0x%04X |",
                       cycle, state_name, oe_r, sd_data_in, dout_r);

                if (sd_data_in == 0xEDCE) printf(" sd_data_in VALID!");
                if (dout_r == 0xEDCE) printf(" dout_r CAPTURED!");
                if (oe_r) printf(" oe_r=1");

                printf("\n");
                trace_count++;
            }
            found_read = true;
        }

        tick_with_sdram(dut, sdram);

        if (found_read && trace_count >= 40) break;
    }

    printf("\n--- Analysis ---\n");
    printf("Expected behavior:\n");
    printf("  1. oe_r should be 1 during read operation\n");
    printf("  2. sd_data_in should briefly become 0xEDCE\n");
    printf("  3. dout_r should capture 0xEDCE when sd_data_in is valid\n");
    printf("  4. dout_r should HOLD the value 0xEDCE after capture\n\n");

    delete sdram;
    delete dut;
    return 0;
}
