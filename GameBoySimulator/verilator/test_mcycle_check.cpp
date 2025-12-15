// Debug test to check mcycle values during JP instruction
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
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
    printf("=== MCycle Debug Test ===\n\n");

    // Boot ROM: JP $0100
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    boot[0] = 0xC3; boot[1] = 0x00; boot[2] = 0x01;  // JP $0100

    // Cart ROM at 0x0100: NOP, JP $0150, data
    std::vector<uint8_t> rom(32768, 0x00);
    rom[0x0100] = 0x00;  // NOP
    rom[0x0101] = 0xC3; rom[0x0102] = 0x50; rom[0x0103] = 0x01;  // JP $0150
    rom[0x0150] = 0x00;  // NOP at destination

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

    printf("Cycle | PC   | MCyc | TSt | IR   | Notes\n");
    printf("------|------|------|-----|------|------\n");

    uint16_t prev_pc = 0;
    uint8_t prev_mcycle = 0, prev_tstate = 0;
    bool found_0100 = false;
    int logged = 0;

    for (int cycle = 0; cycle < 50000 && logged < 100; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t ir = dut->dbg_cpu_ir;

        if (!found_0100 && pc == 0x0100) {
            found_0100 = true;
            printf("=== Found PC=0x0100 ===\n");
        }

        if (found_0100 && pc >= 0x0100 && pc <= 0x0155) {
            // Log on any state change
            bool changed = (pc != prev_pc) || (mcycle != prev_mcycle) || (tstate != prev_tstate);
            
            if (changed) {
                const char* note = "";
                bool is_m1_t4 = (mcycle == 1 && tstate == 16);
                if (is_m1_t4) note = "<-- M1/T4";
                if (pc == 0x0100 && prev_pc != 0x0100) note = "NOP start";
                if (pc == 0x0101 && prev_pc != 0x0101) note = "JP start";
                if (pc == 0x0150 && prev_pc != 0x0150) note = "JP dest";

                printf("%5d | %04X | %4d | %3d | 0x%02X | %s\n",
                    cycle, pc, mcycle, tstate, ir, note);
                logged++;
            }
        }
        prev_pc = pc;
        prev_mcycle = mcycle;
        prev_tstate = tstate;
    }

    delete dut;
    delete sdram;
    return 0;
}
