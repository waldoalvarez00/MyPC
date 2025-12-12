#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    // MisterSDRAMModel ctor takes size in MB (not bytes).
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Diagnostic: ioctl Write Timing Bug ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("Test: Writing to cart ROM via ioctl while monitoring signals...\n\n");

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_addr = 0x0104 >> 1;
    dut->ioctl_dout = 0xAABB;

    printf("Cycle | ioctl_wr | ce_cpu | cart_dl | sdram_we | dn_write* | State\n");
    printf("------|----------|--------|---------|----------|-----------|-------\n");

    // Try writing with ioctl_wr
    for (int i = 0; i < 20; i++) {
        uint8_t ce_cpu = dut->dbg_ce_cpu;
        bool cart_dl = dut->dbg_cart_download;
        bool sdram_we = dut->dbg_sdram_we;

        // Set ioctl_wr on cycles 5-7
        dut->ioctl_wr = (i >= 5 && i <= 7) ? 1 : 0;

        const char* state = "";
        if (i == 5) state = "← ioctl_wr asserted";
        if (i == 6) state = "  (should set ioctl_wait_r)";
        if (i == 7) state = "  (should set dn_write if ce_cpu=1)";
        if (sdram_we) state = "✓ SDRAM WRITE!";

        printf("%5d | %8d | %6d | %7d | %8d | %9s | %s\n",
               i, dut->ioctl_wr, ce_cpu, cart_dl, sdram_we,
               sdram_we ? "YES" : "no",
               state);

        tick_with_sdram(dut, sdram);
    }

    dut->ioctl_download = 0;

    printf("\n--- Analysis ---\n");
    printf("The bug: dn_write is gated by ce_cpu in cart.v line 372:\n");
    printf("  if(speed?ce_cpu2x:ce_cpu) begin\n");
    printf("      dn_write <= ioctl_wait_r;\n");
    printf("\n");
    printf("During ioctl_download, CPU may be paused (ce_cpu=0), so:\n");
    printf("  - ioctl_wr goes high → ioctl_wait_r=1 ✓\n");
    printf("  - But dn_write stays 0 because ce_cpu=0 ✗\n");
    printf("  - sdram_we = cart_download & dn_write = 1 & 0 = 0 ✗\n");
    printf("  - No SDRAM write occurs! ✗\n");
    printf("\n");
    printf("Same bug pattern as:\n");
    printf("  - Boot ROM disable (gb.v:921) - FIXED\n");
    printf("  - LCDC register (video_sim.v:493) - FIXED\n");
    printf("  - Cart download (cart.v:372) - NEEDS FIX\n");

    delete sdram;
    delete dut;
    return 0;
}
