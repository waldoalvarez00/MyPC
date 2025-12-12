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

    printf("=== Diagnostic: dn_write Pulse After Fix ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("Testing ioctl write sequence with cart_download active...\n\n");
    printf("Cycle | ioctl_wr | ioctl_dl | ce_cpu | dn_write | sdram_we | cart_dl | Note\n");
    printf("------|----------|----------|--------|----------|----------|---------|------\n");

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;  // index=0 should trigger cart_download
    dut->ioctl_addr = 0x0104 >> 1;
    dut->ioctl_dout = 0xAABB;

    bool dn_write_pulsed = false;
    bool sdram_we_pulsed = false;

    for (int i = 0; i < 30; i++) {
        uint8_t ce_cpu = dut->dbg_ce_cpu;
        bool dn_write = dut->dbg_dn_write;
        bool sdram_we = dut->dbg_sdram_we;
        bool cart_dl = dut->dbg_cart_download;

        // Assert ioctl_wr on cycles 10-12
        dut->ioctl_wr = (i >= 10 && i <= 12) ? 1 : 0;

        const char* note = "";
        if (i == 10) note = "ioctl_wr asserted";
        if (i == 11) note = "ioctl_wait_r should be set";
        if (i == 12) note = "dn_write should pulse (if fix works!)";
        if (dn_write && !dn_write_pulsed) {
            note = "✓ DN_WRITE PULSED!";
            dn_write_pulsed = true;
        }
        if (sdram_we && !sdram_we_pulsed) {
            note = "✓ SDRAM WRITE!";
            sdram_we_pulsed = true;
        }

        printf("%5d | %8d | %8d | %6d | %8d | %8d | %7d | %s\n",
               i, dut->ioctl_wr, dut->ioctl_download, ce_cpu,
               dn_write, sdram_we, cart_dl, note);

        tick_with_sdram(dut, sdram);
    }

    dut->ioctl_download = 0;

    printf("\n--- Results ---\n");
    if (dn_write_pulsed) {
        printf("✅ PASS: dn_write pulsed after ioctl_wr!\n");
        printf("   Fix is working - dn_write no longer gated by ce_cpu\n");
    } else {
        printf("❌ FAIL: dn_write never pulsed!\n");
        printf("   Fix may not be working or needs different approach\n");
    }

    if (sdram_we_pulsed) {
        printf("✅ PASS: sdram_we pulsed!\n");
        printf("   SDRAM write occurred\n");
    } else {
        printf("❌ FAIL: sdram_we never pulsed!\n");
        printf("   SDRAM write did not occur\n");
    }

    delete sdram;
    delete dut;
    return (dn_write_pulsed && sdram_we_pulsed) ? 0 : 1;
}
