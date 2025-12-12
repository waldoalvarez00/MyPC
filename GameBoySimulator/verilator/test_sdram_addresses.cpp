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

    printf("=== SDRAM Address Mapping Analysis ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("PHASE 1: Writing $CE to cart ROM $0104 via ioctl_download\n");
    printf("Cycle | ioctl_addr | sdram_addr | cart_dl | dn_write | sdram_we\n");
    printf("------|------------|------------|---------|----------|----------\n");

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_addr = 0x0104;        // BYTE address, not word!
    dut->ioctl_dout = 0xEDCE;        // $CE at low byte, $ED at high byte
    dut->ioctl_wr = 0;

    for (int i = 0; i < 10; i++) {
        bool cart_dl = dut->dbg_cart_download;
        bool dn_write = dut->dbg_dn_write;
        bool sdram_we = dut->dbg_sdram_we;
        uint32_t sdram_addr = dut->dbg_sdram_addr;

        if (i == 3) dut->ioctl_wr = 1;
        if (i == 5) dut->ioctl_wr = 0;

        printf("%5d | 0x%08X | 0x%08X | %7d | %8d | %8d",
               i, dut->ioctl_addr, sdram_addr, cart_dl, dn_write, sdram_we);

        if (sdram_we) {
            printf(" ← WRITE to SDRAM addr $%06X", sdram_addr);
        }
        printf("\n");

        tick_with_sdram(dut, sdram);
    }

    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 10);

    printf("\nPHASE 2: CPU reading from cart ROM $0104 during boot\n");
    printf("Cycle | cpu_addr | mbc_addr | sdram_addr | cart_rd | sdram_oe | Data\n");
    printf("------|----------|----------|------------|---------|----------|-----\n");

    // Run until CPU reads from $0104
    bool found_read = false;
    int read_count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        uint32_t mbc_addr = dut->dbg_mbc_addr;
        uint32_t sdram_addr = dut->dbg_sdram_addr;
        bool cart_rd = dut->dbg_cart_rd;
        bool sdram_oe = dut->dbg_sdram_oe;
        uint8_t data = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && cart_rd) {
            if (read_count < 3) {  // Show only first 3 reads
                printf("%5d | %08X | %08X | 0x%08X | %7d | %8d | %02X",
                       cycle, cpu_addr, mbc_addr, sdram_addr, cart_rd, sdram_oe, data);

                if (data == 0xCE) {
                    printf(" ← CORRECT!");
                } else {
                    printf(" ← WRONG (expected $CE)");
                }
                printf("\n");
            }

            found_read = true;
            read_count++;
            if (read_count >= 3) break;  // Stop after 3 reads
        }

        tick_with_sdram(dut, sdram);
    }

    printf("\n--- Analysis ---\n");
    printf("Compare the SDRAM addresses:\n");
    printf("  - Write: ioctl_addr[24:1] should = $0104 >> 1 = $0082\n");
    printf("  - Read: {1'b0, mbc_addr[22:1]} should = {1'b0, $0104 >> 1} = $0082\n");
    printf("\n");
    printf("If these don't match, that's the problem!\n");

    delete sdram;
    delete dut;
    return found_read ? 0 : 1;
}
