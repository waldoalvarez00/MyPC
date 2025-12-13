// GameBoy Doctor Logger - Detailed Cycle Debug
//
// Logs EVERY cycle to see signal transitions

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== Detailed Cycle-by-Cycle Debug ===\n\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Reset
    reset_dut_with_sdram(dut, sdram);

    // Minimal boot
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0x00, sizeof(minimal_boot));
    minimal_boot[0x000] = 0xC3;  // JP 0x0150
    minimal_boot[0x001] = 0x50;
    minimal_boot[0x002] = 0x01;

    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = minimal_boot[addr] | ((uint16_t)minimal_boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);

    // Simple program
    uint8_t test_program[] = {
        0x00,               // 0150: NOP
        0x00,               // 0151: NOP
        0x3E, 0x42,        // 0152: LD A, $42
        0x18, 0xFE,        // 0154: JR -2
    };
    for (int i = 0; i < sizeof(test_program); i++) {
        sdram->write8(0x0150 + i, test_program[i]);
    }

    // Cart header
    const uint8_t logo[48] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E,
    };
    for (int i = 0; i < 48; i++) {
        sdram->write8(0x0104 + i, logo[i]);
    }

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

    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 10000, sdram);

    printf("Logging every cycle from 0 to 200:\n");
    printf("Cyc | PC   | IR | M | T | A  | F  | BC   | SP   | Notes\n");
    printf("--------------------------------------------------------------\n");

    uint16_t prev_pc = 0xFFFF;
    uint8_t prev_ir = 0xFF;
    uint8_t prev_mcycle = 0xFF;

    for (int cycle = 0; cycle < 200; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t curr_pc = dut->dbg_cpu_pc;
        uint8_t curr_ir = dut->dbg_cpu_ir;
        uint8_t curr_mcycle = dut->dbg_cpu_mcycle & 0x07;
        uint8_t curr_tstate = dut->dbg_cpu_tstate & 0x07;
        uint8_t curr_a = dut->dbg_cpu_acc & 0xFF;
        uint8_t curr_f = dut->dbg_cpu_f & 0xFF;
        uint16_t curr_bc = dut->dbg_cpu_bc;
        uint16_t curr_sp = dut->dbg_cpu_sp;

        const char* note = "";
        if (curr_pc != prev_pc) note = "← PC CHANGED";
        else if (curr_ir != prev_ir) note = "← IR CHANGED";
        else if (curr_mcycle != prev_mcycle) note = "← M CHANGED";

        printf("%3d | %04X | %02X | %d | %d | %02X | %02X | %04X | %04X | %s\n",
            cycle, curr_pc, curr_ir, curr_mcycle, curr_tstate,
            curr_a, curr_f, curr_bc, curr_sp, note);

        prev_pc = curr_pc;
        prev_ir = curr_ir;
        prev_mcycle = curr_mcycle;
    }

    printf("\nConclusion:\n");
    printf("  - If M never changes, use PC changes for instruction boundaries\n");
    printf("  - If M changes, look for the pattern (e.g., M1 start = transition to M=1)\n");
    printf("  - Check if IR changes align with instruction boundaries\n");

    delete dut;
    delete sdram;

    return 0;
}
