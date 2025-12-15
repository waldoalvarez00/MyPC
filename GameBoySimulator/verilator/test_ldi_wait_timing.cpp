// Test for LD A,(HL+) Wait_n timing issue
// Verifies hypothesis that Wait_n is low during TState=2 MCycle=2, causing missed HL increment

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

static void upload_boot_rom(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* boot, size_t boot_size) {
    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < (int)boot_size; addr += 2) {
        uint16_t w = boot[addr];
        if (addr + 1 < (int)boot_size) w |= (uint16_t)boot[addr + 1] << 8;
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
}

static void init_cart_ready(Vtop* dut, MisterSDRAMModel* sdram) {
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);
    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 5000, sdram);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== LD A,(HL+) Wait_n Timing Analysis ===\n\n");

    // Test ROM: LD HL, $0150; LD A, (HL+); LD A, (HL+); JP loop
    std::vector<uint8_t> rom(32768, 0x00);
    rom[0x0100] = 0x21; rom[0x0101] = 0x50; rom[0x0102] = 0x01;  // LD HL, $0150
    rom[0x0103] = 0x2A;  // LD A, (HL+)
    rom[0x0104] = 0x2A;  // LD A, (HL+)
    rom[0x0105] = 0xC3; rom[0x0106] = 0x05; rom[0x0107] = 0x01;  // JP $0105

    // Test data at 0x0150
    rom[0x0150] = 0xAA;
    rom[0x0151] = 0xBB;
    rom[0x0152] = 0xCC;

    // Boot ROM: Initialize and jump to 0x0100
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;  // LD SP, $FFFE
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;  // JP $0100

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    printf("Loading cart ROM to SDRAM...\n");
    sdram->loadBinary(0, rom.data(), rom.size());

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    upload_boot_rom(dut, sdram, boot, sizeof(boot));
    init_cart_ready(dut, sdram);

    printf("Releasing reset...\n");
    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("Running simulation to analyze Wait_n timing...\n\n");

    printf("Cycle | PC     | MCyc | TSt | Wait_n | CLKEN | RegWE | HL     | IR   | Notes\n");
    printf("------|--------|------|-----|--------|-------|-------|--------|------|------\n");

    uint16_t prev_pc = 0;
    uint16_t prev_hl = 0;
    bool found_0103 = false;
    int logged = 0;

    // Key tracking: count how many TState=2, MCycle=2 cycles have Wait_n=0
    int ts2_mc2_wait0_count = 0;
    int ts2_mc2_wait1_count = 0;

    for (int cycle = 0; cycle < 100000 && logged < 200; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t ir = dut->dbg_cpu_ir;
        bool wait_n = dut->dbg_sdram_ready;  // sdram_ready is connected to Wait_n
        bool clken = dut->dbg_cpu_clken;
        bool regweh = dut->dbg_cpu_regweh;
        bool regwel = dut->dbg_cpu_regwel;

        // Start tracking at PC=0x0103 (first LD A,(HL+))
        if (!found_0103 && pc == 0x0103) {
            found_0103 = true;
            printf("=== Reached PC=0x0103 (first LD A,(HL+)) ===\n");
        }

        if (found_0103 && pc >= 0x0103 && pc <= 0x0108) {
            // Track TState=2, MCycle=2 Wait_n status
            // TState encoding: internal 1,2,3,4 maps to output (check actual encoding)
            // MCycle encoding: 1,2,4 (one-hot) or 1,2,3 (binary)

            bool is_ts2_mc2 = (tstate == 2 && mcycle == 2);
            if (is_ts2_mc2) {
                if (wait_n)
                    ts2_mc2_wait1_count++;
                else
                    ts2_mc2_wait0_count++;
            }

            // Log state changes or key events
            bool changed = (pc != prev_pc) || (hl != prev_hl);
            bool key_event = is_ts2_mc2 || (regweh && regwel);

            if (changed || key_event) {
                const char* note = "";
                if (pc == 0x0103 && prev_pc != 0x0103) note = "LD A,(HL+) #1 START";
                if (pc == 0x0104 && prev_pc != 0x0104) note = "LD A,(HL+) #2 START";
                if (hl != prev_hl) note = "HL CHANGED!";
                if (is_ts2_mc2 && !wait_n) note = "TS2/MC2 Wait_n=0 - BUG!";
                if (regweh && regwel) note = "RegWE asserted";

                printf("%5d | 0x%04X | %4d | %3d | %6d | %5d | %d%d    | 0x%04X | 0x%02X | %s\n",
                    cycle, pc, mcycle, tstate, wait_n, clken, regweh, regwel, hl, ir, note);
                logged++;
            }
            prev_hl = hl;
        }
        prev_pc = pc;
    }

    // Summary
    printf("\n=== Summary ===\n");
    printf("TState=2, MCycle=2 with Wait_n=1: %d cycles\n", ts2_mc2_wait1_count);
    printf("TState=2, MCycle=2 with Wait_n=0: %d cycles (PROBLEM!)\n", ts2_mc2_wait0_count);
    printf("Final HL: 0x%04X (expected 0x0152)\n", dut->dbg_cpu_hl);

    if (dut->dbg_cpu_hl == 0x0152) {
        printf("\n*** PASS: HL incremented correctly! ***\n");
    } else if (ts2_mc2_wait0_count > 0) {
        printf("\n*** CONFIRMED BUG: Wait_n was low during TState=2, MCycle=2 ***\n");
        printf("    This prevented the register write enable from being asserted.\n");
    } else {
        printf("\n*** FAIL: HL = 0x%04X (expected 0x0152) - different root cause ***\n", dut->dbg_cpu_hl);
    }

    delete dut;
    delete sdram;

    return 0;
}
