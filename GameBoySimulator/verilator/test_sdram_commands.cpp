#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

// SDRAM command decoder
const char* decode_sdram_cmd(bool cs, bool ras, bool cas, bool we) {
    uint8_t cmd = (cs << 3) | (ras << 2) | (cas << 1) | we;
    switch (cmd) {
        case 0b0111: return "NOP  ";
        case 0b0110: return "BST  ";
        case 0b0101: return "READ ";
        case 0b0100: return "WRITE";
        case 0b0011: return "ACT  ";
        case 0b0010: return "PRE  ";
        case 0b0001: return "REF  ";
        case 0b0000: return "MRS  ";
        default:     return "XXXX ";
    }
}

int main() {
    Vtop* dut = new Vtop;
    // MisterSDRAMModel ctor takes size in MB (not bytes).
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency
    sdram->debug = true;  // Enable SDRAM model debug output

    printf("=== SDRAM Command Trace ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("PHASE 1: Write $CE to cart ROM $0104 via ioctl_download\n\n");

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_addr = 0x0104;
    dut->ioctl_dout = 0xEDCE;
    dut->ioctl_wr = 0;

    printf("Monitoring SDRAM commands during ioctl write...\n");
    printf("Cycle | ioctl_wr | cart_dl | dn_write | sdram_we | sdram_ds | CMD   | addr | bank | dqm  | data\n");
    printf("------|----------|---------|----------|----------|----------|-------|------|------|------|------\n");

    for (int i = 0; i < 20; i++) {
        bool cart_dl = dut->dbg_cart_download;
        bool dn_write = dut->dbg_dn_write;
        bool sdram_we = dut->dbg_sdram_we;
        uint8_t sdram_ds = dut->dbg_sdram_ds;

        const char* cmd = decode_sdram_cmd(dut->sd_cs, dut->sd_ras, dut->sd_cas, dut->sd_we);

        printf("%5d | %8d | %7d | %8d | %8d | 0x%02X     | %s | %04X | %d    | 0x%02X | %04X",
               i, dut->ioctl_wr, cart_dl, dn_write, sdram_we, sdram_ds,
               cmd, dut->sd_addr, dut->sd_ba, dut->sd_dqm, dut->sd_data_out);

        if (strcmp(cmd, "ACT  ") == 0) printf(" ← Activate row");
        if (strcmp(cmd, "WRITE") == 0) printf(" ← Write to SDRAM!");
        printf("\n");

        if (i == 5) dut->ioctl_wr = 1;
        if (i == 7) dut->ioctl_wr = 0;

        tick_with_sdram(dut, sdram);
    }

    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("\nPHASE 2: CPU reads from cart ROM $0104\n\n");
    printf("Monitoring SDRAM commands during CPU read...\n");
    printf("Cycle | cart_rd | sdram_oe | CMD   | addr | bank | Data In | Data CPU\n");
    printf("------|---------|----------|-------|------|------|---------|----------\n");

    bool found_read = false;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool cart_rd = dut->dbg_cart_rd;
        bool sdram_oe = dut->dbg_sdram_oe;
        uint8_t cpu_di = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && cart_rd) {
            const char* cmd = decode_sdram_cmd(dut->sd_cs, dut->sd_ras, dut->sd_cas, dut->sd_we);

            printf("%5d | %7d | %8d | %s | %04X | %d    | %04X    | %02X",
                   cycle, cart_rd, sdram_oe,
                   cmd, dut->sd_addr, dut->sd_ba, dut->sd_data_in, cpu_di);

            if (strcmp(cmd, "ACT  ") == 0) printf(" ← Activate row");
            if (strcmp(cmd, "READ ") == 0) printf(" ← Read from SDRAM");
            if (cpu_di == 0xCE) printf(" ✓ CORRECT!");
            printf("\n");

            found_read = true;
            if (cycle > 16550) break;
        }

        tick_with_sdram(dut, sdram);
    }

    printf("\n--- Analysis ---\n");
    printf("Check if SDRAM controller is issuing:\n");
    printf("1. ACT command to activate row\n");
    printf("2. READ/WRITE command to access data\n");
    printf("\n");
    printf("SDRAM Statistics:\n");
    printf("  Reads: %lu, Writes: %lu\n", sdram->read_count, sdram->write_count);
    printf("  Row hits: %lu, Row misses: %lu\n", sdram->row_hits, sdram->row_misses);

    delete sdram;
    delete dut;
    return found_read ? 0 : 1;
}
