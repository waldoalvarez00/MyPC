#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);  // 8 MB

    // CRITICAL: Set realistic CAS latency instead of 0!
    sdram->cas_latency = 2;  // CAS-2 (realistic for SDRAM)
    sdram->debug = true;  // Enable debug output

    printf("=== Test with Realistic SDRAM Latency ===\n");
    printf("CAS Latency: %d cycles\n\n", sdram->cas_latency);

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

    printf("\nStep 2: CPU reads from cart ROM $0104\n");
    printf("Watching for sd_data_in and cpu_di:\n\n");

    printf("Cycle | sd_data_in | dout_r | cpu_di | Note\n");
    printf("------|------------|--------|--------|------\n");

    bool found = false;
    int count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool cart_rd = dut->dbg_cart_rd;
        uint16_t sd_data_in = dut->sd_data_in;
        uint16_t dout_r = dut->dbg_sdram_dout_r;
        uint8_t cpu_di = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && (cart_rd || sd_data_in != 0 || cpu_di != 0)) {
            if (count < 50) {
                printf("%5d | 0x%04X     | 0x%04X | 0x%02X   |",
                       cycle, sd_data_in, dout_r, cpu_di);

                if (sd_data_in == 0xEDCE) printf(" DATA ARRIVES!");
                if (dout_r == 0xEDCE) printf(" CAPTURED!");
                if (cpu_di == 0xCE) printf(" ✓ CPU GOT IT!");

                printf("\n");
                count++;
            }
            found = true;
        }

        tick_with_sdram(dut, sdram);
        if (found && count >= 50) break;
    }

    printf("\n--- Results ---\n");
    printf("With CAS latency = %d:\n", sdram->cas_latency);
    printf("  - Data should be stable for multiple cycles\n");
    printf("  - SDRAM controller should have time to capture\n");
    printf("  - CPU should successfully read the data\n\n");

    printf("SDRAM Statistics:\n");
    printf("  Writes: %lu\n", sdram->write_count);
    printf("  Reads: %lu\n", sdram->read_count);

    delete sdram;
    delete dut;
    return 0;
}
