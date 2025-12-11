#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== Cart Ready Signal Test ===\n\n");

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

    printf("  Memory[0x104] = 0x%02X\n", sdram->memory[0x104]);
    printf("  cart_ready after download = %d\n\n", dut->dbg_cart_ready);

    printf("Step 2: Check cart_ready during cart ROM read\n\n");
    printf("Cycle | cart_ready | rom_do | cart_do | cpu_di |\n");
    printf("------|------------|--------|---------|--------|\n");

    bool found = false;
    int count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool cart_rd = dut->dbg_cart_rd;
        bool cart_ready = dut->dbg_cart_ready;
        uint8_t rom_do = dut->dbg_rom_do;
        uint8_t cart_do = dut->dbg_cart_do;
        uint8_t cpu_di = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && cart_rd) {
            if (count < 50) {
                printf("%5d | %10d | 0x%02X   | 0x%02X    | 0x%02X   |",
                       cycle, cart_ready, rom_do, cart_do, cpu_di);

                if (!cart_ready) printf(" ← cart_ready=0!");
                if (rom_do == 0xCE && cart_do == 0x00) printf(" ← BLOCKED by ~cart_ready!");

                printf("\n");
                count++;
            }
            found = true;
        }

        tick_with_sdram(dut, sdram);
        if (found && count >= 50) break;
    }

    printf("\n--- Analysis ---\n");
    printf("cart.v line 389: if (~cart_ready) cart_do_r = 8'h00;\n");
    printf("If cart_ready=0, all cart reads return 0x00!\n");

    delete sdram;
    delete dut;
    return 0;
}
