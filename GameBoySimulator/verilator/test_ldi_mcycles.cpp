// Debug test for LD A,(HL+) instruction - trace MCycles
// Traces internal mcycles signal to find why instruction only runs M1

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

    printf("=== LD A,(HL+) MCycles Debug Test ===\n\n");

    // ROM layout at 0x0100:
    //   0x0100: LD HL, $0150  (21 50 01)
    //   0x0103: LD A, (HL+)   (2A)
    //   0x0104: LD A, (HL+)   (2A)
    //   0x0105: JP $0105      (C3 05 01)
    std::vector<uint8_t> rom(32768, 0x00);
    rom[0x0100] = 0x21; rom[0x0101] = 0x50; rom[0x0102] = 0x01;  // LD HL, $0150
    rom[0x0103] = 0x2A;  // LD A, (HL+) #1
    rom[0x0104] = 0x2A;  // LD A, (HL+) #2
    rom[0x0105] = 0xC3; rom[0x0106] = 0x05; rom[0x0107] = 0x01;  // JP $0105

    // Test data at 0x0150
    rom[0x0150] = 0xAA;
    rom[0x0151] = 0xBB;
    rom[0x0152] = 0xCC;

    // Boot ROM: Jump to 0x0100
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

    printf("Running simulation...\n\n");

    uint16_t prev_pc = 0;
    uint16_t prev_hl = 0;
    uint8_t prev_mcycle = 0;
    uint8_t prev_mcycles = 0;
    bool found_0100 = false;
    int logged = 0;

    printf("Cyc  | PC   | IR   | MCyc | TSt  | mcycles | mcycles_d | HL   | A    | Notes\n");
    printf("-----|------|------|------|------|---------|-----------|------|------|------\n");

    for (int cycle = 0; cycle < 100000 && logged < 200; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t mcycles = dut->dbg_cpu_mcycles;
        uint8_t mcycles_d = dut->dbg_cpu_mcycles_d;
        uint8_t a = dut->dbg_cpu_acc;

        if (!found_0100 && pc == 0x0100) {
            found_0100 = true;
            printf("=== Reached PC=0x0100 ===\n");
        }

        if (found_0100 && pc >= 0x0100 && pc <= 0x0108) {
            bool changed = (pc != prev_pc) || (mcycle != prev_mcycle) ||
                          (hl != prev_hl) || (mcycles != prev_mcycles);

            // Log at instruction boundaries or state changes
            if (changed || (pc == 0x0103 || pc == 0x0104)) {
                const char* note = "";
                if (pc == 0x0100 && prev_pc != 0x0100) note = "LD HL start";
                if (pc == 0x0103 && prev_pc != 0x0103) note = "LDI A,(HL+) #1";
                if (pc == 0x0104 && prev_pc == 0x0103) note = "LDI A,(HL+) #2";
                if (pc == 0x0105 && prev_pc == 0x0104) note = "JP loop";
                if (hl != prev_hl) {
                    static char buf[64];
                    snprintf(buf, sizeof(buf), "HL: %04X->%04X", prev_hl, hl);
                    note = buf;
                }
                if (mcycles != prev_mcycles) {
                    static char buf[64];
                    snprintf(buf, sizeof(buf), "mcycles: %d->%d", prev_mcycles, mcycles);
                    note = buf;
                }

                printf("%4d | %04X | 0x%02X | 0x%02X | 0x%02X | %7d | %9d | %04X | 0x%02X | %s\n",
                    cycle, pc, ir, mcycle, tstate, mcycles, mcycles_d, hl, a, note);
                logged++;
            }

            prev_hl = hl;
            prev_mcycles = mcycles;
        }

        prev_pc = pc;
        prev_mcycle = mcycle;
    }

    // Final state
    printf("\n=== Final State ===\n");
    printf("PC: 0x%04X\n", dut->dbg_cpu_pc);
    printf("HL: 0x%04X (expected 0x0152)\n", dut->dbg_cpu_hl);
    printf("A:  0x%02X (expected 0xBB)\n", dut->dbg_cpu_acc);

    bool pass = (dut->dbg_cpu_hl == 0x0152);
    printf("\n%s\n", pass ? "*** PASS ***" : "*** FAIL ***");

    delete dut;
    delete sdram;

    return pass ? 0 : 1;
}
