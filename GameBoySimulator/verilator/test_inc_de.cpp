// GameBoy RTL Unit Test - INC DE / Sequential ROM Byte Reads
//
// The DMG boot ROM relies on `LD A,(DE)` + `INC DE` to walk the cartridge header
// (Nintendo logo at 0x0104..). If `INC DE` is broken or the external bus doesn't
// advance reads correctly, the logo transfer fails and the LCD can appear all white.

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

static void upload_boot_jump_to_0150(Vtop* dut, MisterSDRAMModel* sdram) {
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    // Jump straight to our test program in cartridge ROM.
    boot[0x000] = 0xC3;  // JP 0x0150
    boot[0x001] = 0x50;
    boot[0x002] = 0x01;

    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = boot[addr] | ((uint16_t)boot[addr + 1] << 8);
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
    // Pulse download high (no writes), then pulse ioctl_wr once with download low.
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

    TestResults results;
    results.set_suite("INC DE");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // ROM with known bytes at 0x0104..0x0105 and a tiny program at 0x0150.
    uint8_t rom[32768];
    memset(rom, 0x00, sizeof(rom));
    // Standard cartridge entrypoint (should be skipped by our boot ROM jump, but keep it valid).
    rom[0x0100] = 0xC3;
    rom[0x0101] = 0x50;
    rom[0x0102] = 0x01;
    // Nintendo logo header bytes (required for cart_ready and used by DMG boot ROM).
    const uint8_t logo[48] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E,
    };
    memcpy(&rom[0x0104], logo, sizeof(logo));

    // Program @ 0x0150:
    //   LD DE,0104
    //   LD A,(DE)      ; expect 0xCE
    //   INC DE         ; expect DE=0105
    //   LD A,(DE)      ; expect 0xED
    //   HALT
    int p = 0x0150;
    rom[p++] = 0x11; rom[p++] = 0x04; rom[p++] = 0x01;  // LD DE,0104
    rom[p++] = 0x1A;                                   // LD A,(DE)
    rom[p++] = 0x13;                                   // INC DE
    rom[p++] = 0x1A;                                   // LD A,(DE)
    rom[p++] = 0x76;                                   // HALT

    sdram->loadBinary(0, rom, sizeof(rom));

    // Hold reset while wiring boot/cart, then release.
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    upload_boot_jump_to_0150(dut, sdram);
    init_cart_ready(dut, sdram);

    run_cycles_with_sdram(dut, sdram, 200);
    dut->reset = 0;

    // Run until HALT is fetched (PC increments to 0x0157 after fetching 0x0156).
    const int max_cycles = 200000;
    bool halted = false;
    bool saw_0104 = false;
    bool saw_0105 = false;
    for (int i = 0; i < max_cycles; i++) {
        tick_with_sdram(dut, sdram);

        // Trace the first time we see each header byte address on the external bus.
        if (dut->dbg_sel_ext_bus && !dut->dbg_cpu_rd_n && !dut->dbg_sel_boot_rom) {
            const uint16_t a = (uint16_t)dut->dbg_cpu_addr;
            if ((a == 0x0104 && !saw_0104) || (a == 0x0105 && !saw_0105)) {
                printf("  [ROM RD] A=$%04X mbc=$%06X sdram_addr=$%06X sdram_do=$%04X rom_do=$%02X cart_do=$%02X di=$%02X di_lat=$%02X CLKEN=%d\n",
                       a,
                       (unsigned)dut->dbg_mbc_addr,
                       (unsigned)dut->dbg_sdram_addr,
                       (unsigned)dut->dbg_sdram_do,
                       (unsigned)dut->dbg_rom_do,
                       (unsigned)dut->dbg_cart_do,
                       (unsigned)dut->dbg_cpu_di,
                       (unsigned)dut->dbg_cpu_di_latched,
                       dut->dbg_cpu_clken);
                if (a == 0x0104) saw_0104 = true;
                if (a == 0x0105) saw_0105 = true;
            }
        }
        if (dut->dbg_cpu_pc == 0x0157 && (uint8_t)dut->dbg_cpu_ir == 0x76) { halted = true; break; }
    }

    results.check(halted, "Reached HALT");
    results.check_eq(dut->dbg_cpu_de, 0x0105, "DE incremented to 0x0105");
    results.check(saw_0104, "Saw external read at 0x0104");
    results.check(saw_0105, "Saw external read at 0x0105");
    results.check_eq(dut->dbg_cpu_acc, 0xED, "Second LD A,(DE) reads 0xED");

    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
