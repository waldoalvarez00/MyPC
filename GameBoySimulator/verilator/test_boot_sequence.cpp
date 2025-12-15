// Test the boot ROM sequence: LD HL,$01B0 → PUSH HL → POP AF
// After POP AF, A should be $01 (from H) and F should be $B0 (from L)

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

    printf("=== Boot ROM Sequence Test ===\n\n");
    printf("Testing: LD SP,$FFFE → LD HL,$01B0 → PUSH HL → POP AF → JP $0100\n");
    printf("Expected: After POP AF, A=$01 (from H), F=$B0 (from L)\n\n");

    // ROM at 0x0100: infinite loop
    std::vector<uint8_t> rom(32768, 0x00);
    rom[0x0100] = 0xC3; rom[0x0101] = 0x00; rom[0x0102] = 0x01;  // JP $0100

    // Boot ROM: The sequence we want to test
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;  // LD SP, $FFFE
    boot[i++] = 0x21; boot[i++] = 0xB0; boot[i++] = 0x01;  // LD HL, $01B0 (H=$01, L=$B0)
    boot[i++] = 0xE5;                                        // PUSH HL
    boot[i++] = 0xF1;                                        // POP AF
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;  // JP $0100

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

    printf("Boot ROM bytes:\n");
    for (int j = 0; j < i; j++) {
        printf("  0x%02X: 0x%02X\n", j, boot[j]);
    }
    printf("\n");

    printf("Running simulation...\n\n");

    printf("Cyc  | PC   | IR   | SP   | A    | F    | H    | L    | HL   | Notes\n");
    printf("-----|------|------|------|------|------|------|------|------|------\n");

    uint16_t prev_pc = 0xFFFF;
    bool reached_cart = false;
    uint8_t final_a = 0, final_f = 0;

    for (int cycle = 0; cycle < 200000 && !reached_cart; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint16_t sp = dut->dbg_cpu_sp;
        uint8_t a = dut->dbg_cpu_acc;
        uint8_t f = dut->dbg_cpu_f;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t h = (hl >> 8) & 0xFF;
        uint8_t l = hl & 0xFF;

        // Log on PC transitions in boot ROM range
        if (pc != prev_pc && pc < 0x0100) {
            const char* note = "";
            if (pc == 0x0000) note = "LD SP,$FFFE";
            if (pc == 0x0003) note = "LD HL,$01B0";
            if (pc == 0x0006) note = "PUSH HL (should push $01B0)";
            if (pc == 0x0007) note = "POP AF (should set A=$01, F=$B0)";
            if (pc == 0x0008) note = "JP $0100";

            printf("%4d | %04X | 0x%02X | %04X | 0x%02X | 0x%02X | 0x%02X | 0x%02X | %04X | %s\n",
                cycle, pc, ir, sp, a, f, h, l, hl, note);
        }

        // Log when we first reach $0100
        if (pc == 0x0100 && prev_pc != 0x0100) {
            final_a = a;
            final_f = f;
            printf("%4d | %04X | 0x%02X | %04X | 0x%02X | 0x%02X | 0x%02X | 0x%02X | %04X | Cartridge entry!\n",
                cycle, pc, ir, sp, a, f, h, l, hl);
            reached_cart = true;
        }

        prev_pc = pc;
    }

    // Check stack memory after PUSH
    printf("\n=== Stack Memory ===\n");
    uint8_t stack_low = sdram->read_byte(0xFFFC);
    uint8_t stack_high = sdram->read_byte(0xFFFD);
    printf("[$FFFC]: 0x%02X (should be L=0xB0)\n", stack_low);
    printf("[$FFFD]: 0x%02X (should be H=0x01)\n", stack_high);

    printf("\n=== Final State at Cartridge Entry ===\n");
    printf("A: 0x%02X (expected 0x01)\n", final_a);
    printf("F: 0x%02X (expected 0xB0)\n", final_f);

    bool pass = (final_a == 0x01) && (final_f == 0xB0);
    printf("\n%s\n", pass ? "*** PASS ***" : "*** FAIL ***");

    if (!pass) {
        if (final_a != 0x01) printf("  A incorrect: got 0x%02X, expected 0x01\n", final_a);
        if (final_f != 0xB0) printf("  F incorrect: got 0x%02X, expected 0xB0\n", final_f);
    }

    delete dut;
    delete sdram;

    return pass ? 0 : 1;
}
