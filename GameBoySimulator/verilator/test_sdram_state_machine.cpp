#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

// SDRAM state names
const char* state_name(uint8_t state) {
    switch(state) {
        case 0: return "IDLE    ";
        case 1: return "ACTIVATE";
        case 2: return "READ    ";
        case 3: return "WRITE   ";
        case 4: return "REFRESH ";
        case 5: return "PRECHRG ";
        default: return "UNKNOWN ";
    }
}

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);  // 8 MB
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== SDRAM State Machine Trace ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("PHASE 1: Write $CE to cart ROM $0104 via ioctl_download\n");
    printf("Monitoring SDRAM state machine during WRITE...\n\n");

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_addr = 0x0104;
    dut->ioctl_dout = 0xEDCE;
    dut->ioctl_wr = 0;

    printf("Cycle | State    | sync | oe | we | oe_pend | we_pend | cart_dl | dn_write | sdram_we\n");
    printf("------|----------|------|----|----|---------|---------|---------|----------|---------\n");

    for (int i = 0; i < 30; i++) {
        uint8_t state = dut->dbg_sdram_state;
        bool sync = dut->dbg_sdram_sync;
        bool oe = dut->dbg_sdram_oe;
        bool we = dut->dbg_sdram_we;
        bool oe_pend = dut->dbg_sdram_oe_pending;
        bool we_pend = dut->dbg_sdram_we_pending;
        bool cart_dl = dut->dbg_cart_download;
        bool dn_write = dut->dbg_dn_write;

        printf("%5d | %s | %4d | %2d | %2d | %7d | %7d | %7d | %8d | %8d",
               i, state_name(state), sync, oe, we, oe_pend, we_pend,
               cart_dl, dn_write, we);

        if (i == 5) {
            dut->ioctl_wr = 1;
            printf(" ← ioctl_wr=1");
        }
        if (i == 7) {
            dut->ioctl_wr = 0;
            printf(" ← ioctl_wr=0");
        }
        if (dn_write) printf(" ← DN_WRITE!");
        if (state != 0) printf(" ← STATE CHANGE");

        printf("\n");

        tick_with_sdram(dut, sdram);
    }

    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("\nPHASE 2: CPU reads from cart ROM $0104 during boot\n");
    printf("Monitoring SDRAM state machine during READ...\n\n");

    printf("Cycle | State    | sync | ce_cpu | cart_rd | oe | we | oe_pend | we_pend | Data\n");
    printf("------|----------|------|--------|---------|----|----|---------|---------|-----\n");

    bool found_read = false;
    int trace_count = 0;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool cart_rd = dut->dbg_cart_rd;
        bool oe = dut->dbg_sdram_oe;
        bool we = dut->dbg_sdram_we;
        uint8_t state = dut->dbg_sdram_state;
        bool sync = dut->dbg_sdram_sync;
        bool oe_pend = dut->dbg_sdram_oe_pending;
        bool we_pend = dut->dbg_sdram_we_pending;
        uint8_t ce_cpu = dut->dbg_ce_cpu;
        uint8_t data = dut->dbg_cpu_di;

        if (cpu_addr == 0x0104 && (cart_rd || oe_pend || state != 0)) {
            if (trace_count < 50) {  // Show first 50 cycles
                printf("%5d | %s | %4d | %6d | %7d | %2d | %2d | %7d | %7d | %02X",
                       cycle, state_name(state), sync, ce_cpu, cart_rd, oe, we,
                       oe_pend, we_pend, data);

                if (cart_rd && !oe_pend && !oe) printf(" ← cart_rd HIGH but oe=0!");
                if (cart_rd && oe && !sync) printf(" ← oe=1 but sync=0, state won't advance!");
                if (oe_pend && !sync) printf(" ← oe_pending set but sync=0!");
                if (state == 2) printf(" ← IN READ STATE!");
                if (data == 0xCE) printf(" ← CORRECT DATA!");

                printf("\n");
                trace_count++;
            }
            found_read = true;
        }

        tick_with_sdram(dut, sdram);

        if (found_read && trace_count >= 50) break;
    }

    printf("\n--- Analysis ---\n");
    printf("SDRAM Statistics:\n");
    printf("  Writes: %lu\n", sdram->write_count);
    printf("  Reads: %lu\n\n", sdram->read_count);

    if (sdram->write_count > 0) {
        printf("✅ WRITE path working: State machine advanced through IDLE→ACTIVATE→WRITE\n");
    } else {
        printf("❌ WRITE path broken\n");
    }

    if (sdram->read_count > 0) {
        printf("✅ READ path working: State machine advanced through IDLE→ACTIVATE→READ\n");
    } else {
        printf("❌ READ path broken: Check trace above for why state machine didn't advance\n");
    }

    delete sdram;
    delete dut;
    return (sdram->read_count > 0) ? 0 : 1;
}
