// Test for POP AF instruction bug
// After PUSH HL ($01B0) and POP AF, A should be 0x01 and F should be 0xB0

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

    printf("=== POP AF Bug Test ===\n\n");

    // ROM layout at 0x0100:
    //   0x0100: LD SP, $FFFE  (31 FE FF)
    //   0x0103: LD HL, $01B0  (21 B0 01)
    //   0x0106: PUSH HL       (E5)
    //   0x0107: POP AF        (F1)
    //   0x0108: JP $0108      (C3 08 01) - infinite loop
    std::vector<uint8_t> rom(32768, 0x00);
    int i = 0x0100;
    rom[i++] = 0x31; rom[i++] = 0xFE; rom[i++] = 0xFF;  // LD SP, $FFFE
    rom[i++] = 0x21; rom[i++] = 0xB0; rom[i++] = 0x01;  // LD HL, $01B0 (H=$01, L=$B0)
    rom[i++] = 0xE5;                                      // PUSH HL
    rom[i++] = 0xF1;                                      // POP AF
    rom[i++] = 0xC3; rom[i++] = 0x08; rom[i++] = 0x01;  // JP $0108

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

    // Track state at key points
    uint16_t hl_before_push = 0;
    uint16_t sp_before_push = 0;
    uint16_t sp_after_push = 0;
    uint8_t a_after_pop = 0;
    uint8_t f_after_pop = 0;
    uint16_t sp_after_pop = 0;

    uint16_t prev_pc = 0;
    bool reached_loop = false;

    printf("Cyc  | PC   | SP   | A    | F    | H    | L    | HL   | Notes\n");
    printf("-----|------|------|------|------|------|------|------|------\n");

    for (int cycle = 0; cycle < 100000 && !reached_loop; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t sp = dut->dbg_cpu_sp;
        uint8_t a = dut->dbg_cpu_acc;
        uint8_t f = dut->dbg_cpu_f;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t h = (hl >> 8) & 0xFF;
        uint8_t l = hl & 0xFF;
        uint8_t ir = dut->dbg_cpu_ir;

        // Log PC transitions
        if (pc != prev_pc && pc >= 0x0100 && pc <= 0x010B) {
            const char* note = "";
            if (pc == 0x0100) note = "Start";
            if (pc == 0x0103) note = "LD HL,$01B0";
            if (pc == 0x0106) {
                note = "PUSH HL";
                hl_before_push = hl;
                sp_before_push = sp;
            }
            if (pc == 0x0107) {
                note = "POP AF";
                sp_after_push = sp;
            }
            if (pc == 0x0108) {
                note = "JP loop";
                a_after_pop = a;
                f_after_pop = f;
                sp_after_pop = sp;
                reached_loop = true;
            }

            printf("%4d | %04X | %04X | 0x%02X | 0x%02X | 0x%02X | 0x%02X | %04X | %s\n",
                cycle, pc, sp, a, f, h, l, hl, note);
        }
        prev_pc = pc;
    }

    // Final analysis
    printf("\n=== Analysis ===\n");
    printf("HL before PUSH: 0x%04X (H=0x%02X, L=0x%02X)\n",
           hl_before_push, (hl_before_push>>8)&0xFF, hl_before_push&0xFF);
    printf("SP before PUSH: 0x%04X\n", sp_before_push);
    printf("SP after PUSH:  0x%04X (expected: 0x%04X)\n", sp_after_push, sp_before_push - 2);
    printf("SP after POP:   0x%04X (expected: 0x%04X)\n", sp_after_pop, sp_before_push);
    printf("\n");
    printf("A after POP AF: 0x%02X (expected: 0x%02X from H)\n", a_after_pop, (hl_before_push>>8)&0xFF);
    printf("F after POP AF: 0x%02X (expected: 0x%02X from L)\n", f_after_pop, hl_before_push&0xFF);

    // Check stack memory
    printf("\n=== Stack Memory Check ===\n");
    uint8_t stack_low = sdram->read_byte(0xFFFC);
    uint8_t stack_high = sdram->read_byte(0xFFFD);
    printf("Stack [$FFFC]: 0x%02X (should be L=0x%02X)\n", stack_low, hl_before_push&0xFF);
    printf("Stack [$FFFD]: 0x%02X (should be H=0x%02X)\n", stack_high, (hl_before_push>>8)&0xFF);

    bool pass = (a_after_pop == 0x01) && (f_after_pop == 0xB0);

    printf("\n%s\n", pass ? "*** PASS ***" : "*** FAIL ***");
    if (!pass) {
        if (a_after_pop != 0x01) {
            printf("  A incorrect: got 0x%02X, expected 0x01\n", a_after_pop);
        }
        if (f_after_pop != 0xB0) {
            printf("  F incorrect: got 0x%02X, expected 0xB0\n", f_after_pop);
        }
    }

    delete dut;
    delete sdram;

    return pass ? 0 : 1;
}
