// Test for LD HL,nn instruction timing bug
// H register appears to load one instruction late

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

    printf("=== LD HL,nn Timing Bug Test ===\n\n");

    // ROM layout at 0x0100:
    //   0x0100: LD HL, $1234  (21 34 12) - L=$34, H=$12
    //   0x0103: NOP           (00)
    //   0x0104: NOP           (00)
    //   0x0105: JP $0105      (C3 05 01) - infinite loop
    std::vector<uint8_t> rom(32768, 0x00);
    int i = 0x0100;
    rom[i++] = 0x21; rom[i++] = 0x34; rom[i++] = 0x12;  // LD HL, $1234
    rom[i++] = 0x00;                                      // NOP
    rom[i++] = 0x00;                                      // NOP
    rom[i++] = 0xC3; rom[i++] = 0x05; rom[i++] = 0x01;  // JP $0105

    // Boot ROM: Jump to 0x0100
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    boot[0] = 0xC3; boot[1] = 0x00; boot[2] = 0x01;  // JP $0100

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    sdram->loadBinary(0, rom.data(), rom.size());

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

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("Running simulation...\n\n");
    printf("Expected: After LD HL,$1234, HL should be $1234 (H=$12, L=$34)\n\n");

    uint16_t prev_pc = 0;
    bool reached_loop = false;
    int logged = 0;

    printf("Cyc  | PC   | MCyc | TSt  | IR   | H    | L    | HL   | Notes\n");
    printf("-----|------|------|------|------|------|------|------|------\n");

    for (int cycle = 0; cycle < 100000 && !reached_loop; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t h = (hl >> 8) & 0xFF;
        uint8_t l = hl & 0xFF;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;

        // Log on PC transition only for our range
        if (pc != prev_pc && pc >= 0x0100 && pc <= 0x0108) {
            const char* note = "";
            if (pc == 0x0100) note = "LD HL,$1234 start";
            if (pc == 0x0103) {
                note = "NOP #1 (HL should be $1234)";
                if (hl != 0x1234) note = "NOP #1 - HL WRONG!";
            }
            if (pc == 0x0104) note = "NOP #2";
            if (pc == 0x0105) {
                note = "JP loop";
                reached_loop = true;
            }

            int mc = 0, ts = 0;
            for (int b = 0; b < 7; b++) {
                if (mcycle & (1 << b)) mc = b + 1;
                if (tstate & (1 << b)) ts = b + 1;
            }

            printf("%4d | %04X | M%d   | T%d   | 0x%02X | 0x%02X | 0x%02X | %04X | %s\n",
                cycle, pc, mc, ts, ir, h, l, hl, note);
            logged++;
        }
        prev_pc = pc;
    }

    // Final check
    uint16_t final_hl = dut->dbg_cpu_hl;
    printf("\n=== Final State ===\n");
    printf("HL: 0x%04X (expected 0x1234)\n", final_hl);
    printf("H:  0x%02X (expected 0x12)\n", (final_hl >> 8) & 0xFF);
    printf("L:  0x%02X (expected 0x34)\n", final_hl & 0xFF);

    bool pass = (final_hl == 0x1234);
    printf("\n%s\n", pass ? "*** PASS ***" : "*** FAIL ***");

    delete dut;
    delete sdram;

    return pass ? 0 : 1;
}
