// Detailed trace for LD A,(HL+) instruction bug
// Logs EVERY cycle to catch timing issues

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

    printf("=== LD A,(HL+) Detailed Trace ===\n\n");

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

    // Print ROM contents to verify
    printf("ROM contents:\n");
    printf("  0x0100: 0x%02X (expect 0x21 - LD HL)\n", rom[0x0100]);
    printf("  0x0101: 0x%02X (expect 0x50)\n", rom[0x0101]);
    printf("  0x0102: 0x%02X (expect 0x01)\n", rom[0x0102]);
    printf("  0x0103: 0x%02X (expect 0x2A - LD A,(HL+))\n", rom[0x0103]);
    printf("  0x0104: 0x%02X (expect 0x2A - LD A,(HL+))\n", rom[0x0104]);
    printf("\n");

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

    // Verify SDRAM contents
    printf("SDRAM contents at relevant addresses:\n");
    printf("  SDRAM[0x0103] = 0x%02X (expect 0x2A)\n", sdram->read_byte(0x0103));
    printf("  SDRAM[0x0104] = 0x%02X (expect 0x2A)\n", sdram->read_byte(0x0104));
    printf("\n");

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

    bool found_0100 = false;
    int logged = 0;

    printf("Cyc  | PC   | Addr | IR   | DI   | MCyc | TSt | mcy | Notes\n");
    printf("-----|------|------|------|------|------|-----|-----|------\n");

    uint8_t prev_tstate = 0;
    for (int cycle = 0; cycle < 200000 && logged < 200; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t di = dut->dbg_cpu_di;  // Data in from memory
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t mcycles = dut->dbg_cpu_mcycles;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t a = dut->dbg_cpu_acc;
        bool cpu_clken = dut->dbg_cpu_clken;

        if (!found_0100 && pc == 0x0100) {
            found_0100 = true;
            printf("=== Reached PC=0x0100 ===\n");
        }

        // Only log on tstate transitions (when cpu advances)
        bool tstate_changed = (tstate != prev_tstate);
        prev_tstate = tstate;

        // Log only on tstate changes when PC is in our range
        if (found_0100 && pc >= 0x0100 && pc <= 0x0108 && tstate_changed) {
            const char* note = "";
            if (pc == 0x0103 && ir == 0x2A) note = "LDI correct!";
            if (pc == 0x0103 && ir != 0x2A) note = "LDI IR wrong!";
            if (pc == 0x0104 && ir == 0x2A) note = "LDI #2";

            // Decode mcycle and tstate one-hot values
            int mc_num = 0, ts_num = 0;
            for (int b = 0; b < 7; b++) {
                if (mcycle & (1 << b)) mc_num = b + 1;
                if (tstate & (1 << b)) ts_num = b + 1;
            }

            printf("%4d | %04X | %04X | 0x%02X | 0x%02X | M%d   | T%d  | %d   | %s HL=%04X A=%02X\n",
                cycle, pc, addr, ir, di, mc_num, ts_num, mcycles, note, hl, a);
            logged++;
        }
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
