#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);  // 8 MB
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Data Path Trace ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Write data to SDRAM
    printf("Step 1: Write $CE to SDRAM memory[$0104]\n");
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

    printf("  SDRAM memory[0x104] = 0x%02X (expect 0xCE)\n", sdram->memory[0x104]);
    printf("  SDRAM memory[0x105] = 0x%02X (expect 0xED)\n\n", sdram->memory[0x105]);

    printf("Step 2: CPU reads from cart ROM $0104\n");
    printf("Monitoring complete data path...\n\n");

    printf("Cycle | cart_rd | sdram_oe | sd_data_in | sdram_do | cpu_di | mem[0x104]\n");
    printf("------|---------|----------|------------|----------|--------|----------\n");

    bool found_read = false;
    int trace_count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool cart_rd = dut->dbg_cart_rd;
        bool sdram_oe = dut->dbg_sdram_oe;
        uint16_t sd_data_in = dut->sd_data_in;  // Data from SDRAM model
        uint8_t cpu_di = dut->dbg_cpu_di;       // Data CPU receives
        uint8_t mem_byte = sdram->memory[0x104]; // Actual memory value

        if (cpu_addr == 0x0104 && cart_rd) {
            if (trace_count < 30) {
                printf("%5d | %7d | %8d | 0x%04X     | ???????? | 0x%02X   | 0x%02X",
                       cycle, cart_rd, sdram_oe, sd_data_in, cpu_di, mem_byte);

                if (sd_data_in == 0xEDCE) printf(" ← sd_data_in CORRECT!");
                else if (sd_data_in == 0) printf(" ← sd_data_in is ZERO!");

                if (cpu_di == 0xCE) printf(" ← CPU got correct byte!");
                else printf(" ← CPU got wrong byte!");

                printf("\n");
                trace_count++;
            }
            found_read = true;
        }

        tick_with_sdram(dut, sdram);

        if (found_read && trace_count >= 30) break;
    }

    printf("\n--- Data Path Analysis ---\n");
    printf("Data flow should be:\n");
    printf("  1. SDRAM model memory[0x104] = 0x%02X\n", sdram->memory[0x104]);
    printf("  2. Model returns via sd_data_in\n");
    printf("  3. sdram_ctrl.dout = sd_data_in (when in READ state)\n");
    printf("  4. gameboy_sim.sdram_do = sdram_ctrl.dout\n");
    printf("  5. gb.cart_do = sdram_do (for cart ROM addresses)\n");
    printf("  6. CPU reads cart_do\n\n");

    printf("Check trace above to see where data is lost!\n");

    delete sdram;
    delete dut;
    return 0;
}
