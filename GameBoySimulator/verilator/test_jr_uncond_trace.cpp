#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <stdio.h>
#include <string.h>

static void setup_system(Vtop* dut, MisterSDRAMModel* sdram, uint8_t* rom, size_t rom_size) {
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;

    sdram->loadBinary(0, rom, rom_size);

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t word = minimal_boot[addr];
        if (addr + 1 < 256) word |= (minimal_boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    for (int i = 0; i < 10; i++) {
        dut->ioctl_addr = i;
        dut->ioctl_wr = 1;
        run_cycles_with_sdram(dut, sdram, 64);
        dut->ioctl_wr = 0;
        run_cycles_with_sdram(dut, sdram, 64);
        if (dut->dbg_cart_ready) break;
    }
    dut->ioctl_download = 0;

    for (int cycle = 0; cycle < 50000; cycle++) {
        tick_with_sdram(dut, sdram);
        if (!dut->dbg_boot_rom_enabled) break;
    }
}

static const char* decode_mcycle(uint8_t mcycle) {
    if (mcycle & 0x01) return "M1";
    if (mcycle & 0x02) return "M2";
    if (mcycle & 0x04) return "M3";
    if (mcycle & 0x08) return "M4";
    if (mcycle & 0x10) return "M5";
    if (mcycle & 0x20) return "M6";
    if (mcycle & 0x40) return "M7";
    return "??";
}

static const char* decode_tstate(uint8_t tstate) {
    if (tstate & 0x01) return "T1";
    if (tstate & 0x02) return "T2";
    if (tstate & 0x04) return "T3";
    if (tstate & 0x08) return "T4";
    if (tstate & 0x10) return "T5";
    if (tstate & 0x20) return "T6";
    if (tstate & 0x40) return "T7";
    return "??";
}

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150
    rom[0x150] = 0x00;  // NOP
    rom[0x151] = 0x00;  // NOP
    rom[0x152] = 0x18; rom[0x153] = 0x02;  // JR +2
    rom[0x154] = 0x76;  // HALT skip
    rom[0x155] = 0x76;  // HALT skip
    rom[0x156] = 0x00;  // NOP target
    rom[0x157] = 0x76;  // HALT success

    setup_system(dut, sdram, rom, sizeof(rom));

    printf("\n=== Unconditional JR Trace (expect HALT at $0157) ===\n");
    printf("sysclk  PC     IR   DI   MCd MC  MC  TS\n");
    printf("------  ----   ---  ---  --- --  --  --\n");

    uint16_t last_pc = 0xFFFF;
    uint8_t last_ir = 0xFF;
    uint8_t last_mcycle = 0;
    uint8_t last_tstate = 0;

    for (int cycle = 0; cycle < 600000; cycle++) {
        tick_with_sdram(dut, sdram);
        if (dut->dbg_boot_rom_enabled) continue;

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t di = dut->dbg_cpu_di;
        uint8_t mcd = dut->dbg_cpu_mcycles_d;
        uint8_t mc = dut->dbg_cpu_mcycles;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;

        bool state_changed = (pc != last_pc) || (ir != last_ir) || (mcycle != last_mcycle) || (tstate != last_tstate);
        if (state_changed && pc >= 0x014E && pc <= 0x0160) {
            printf("%6d  $%04X  $%02X $%02X   %d   %d  %-2s  %-2s\n",
                   cycle, pc, ir, di, mcd, mc, decode_mcycle(mcycle), decode_tstate(tstate));
        }

        last_pc = pc;
        last_ir = ir;
        last_mcycle = mcycle;
        last_tstate = tstate;

        if (pc == 0x0157) {
            printf("\n✅ HALT reached at $0157\n");
            break;
        }
        if (pc == 0x0154 || pc == 0x0155) {
            // still allow some time, but if we fetch HALT here, it's likely wrong
            if (ir == 0x76 && mcycle & 0x01) {
                printf("\n❌ HALT fetched at $%04X (jump short/not taken)\n", pc);
                break;
            }
        }
    }

    delete sdram;
    delete dut;
    return 0;
}

