#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

const char* state_name(uint8_t state) {
    switch(state) {
        case 0: return "IDLE";
        case 1: return "ACT ";
        case 2: return "READ";
        case 3: return "WR  ";
        case 4: return "REF ";
        case 5: return "PRE ";
        default: return "??? ";
    }
}

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);  // 8 MB
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Timing Analysis ===\n\n");

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

    printf("CPU reads from cart ROM $0104:\n");
    printf("Watch for when state=READ and when sd_data_in has correct data\n\n");

    printf("Cycle | State | sync | cart_rd | cpu_rd_n | sd_data_in | cpu_di | Note\n");
    printf("------|-------|------|---------|----------|------------|--------|------\n");

    bool found_read = false;
    int trace_count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool cart_rd = dut->dbg_cart_rd;
        bool cpu_rd_n = dut->dbg_cpu_rd_n;
        uint8_t state = dut->dbg_sdram_state;
        bool sync = dut->dbg_sdram_sync;
        uint16_t sd_data_in = dut->sd_data_in;
        uint8_t cpu_di = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && (cart_rd || state == 2 || sd_data_in != 0)) {
            if (trace_count < 40) {
                printf("%5d | %s | %4d | %7d | %8d | 0x%04X     | 0x%02X   |",
                       cycle, state_name(state), sync, cart_rd, cpu_rd_n, sd_data_in, cpu_di);

                if (state == 2) printf(" READ STATE");
                if (sd_data_in == 0xEDCE) printf(" ← DATA VALID!");
                if (cpu_di == 0xCE) printf(" ← CPU GOT IT!");
                if (!cpu_rd_n) printf(" cpu reading");

                printf("\n");
                trace_count++;
            }
            found_read = true;
        }

        tick_with_sdram(dut, sdram);

        if (found_read && trace_count >= 40) break;
    }

    printf("\n--- Analysis ---\n");
    printf("The CPU samples data when cpu_rd_n goes LOW.\n");
    printf("The SDRAM provides valid data when state=READ and sd_data_in is non-zero.\n");
    printf("If these don't align, the CPU will miss the data!\n\n");

    printf("The problem: sd_data_in is only valid for 1 cycle (when READ command returns).\n");
    printf("But CPU might read on a different cycle.\n");
    printf("Solution: sdram_ctrl needs to HOLD the data until CPU reads it.\n");

    delete sdram;
    delete dut;
    return 0;
}
