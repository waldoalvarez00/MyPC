#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <stdio.h>
#include <string.h>

static void setup_system(Vtop* dut, MisterSDRAMModel* sdram, uint8_t* rom, size_t rom_size) {
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;  // LD A,1
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;  // LDH (FF50),A

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

    // Vectors: return immediately
    rom[0x0000] = 0xC9;  // RET
    rom[0x0008] = 0xC9;  // RET

    // Program at $0150: set SP to HRAM top, execute RST $08, then HALT.
    uint16_t pc = 0x150;
    rom[pc++] = 0x31; rom[pc++] = 0xFE; rom[pc++] = 0xFF;  // LD SP,$FFFE
    uint16_t rst_pc = pc;
    rom[pc++] = 0xC7;                                      // RST $00
    rom[pc++] = 0x76;                                      // HALT
    uint16_t halt_pc = pc - 1;

    setup_system(dut, sdram, rom, sizeof(rom));

    printf("\n=== RST $00 Trace (RST at $%04X, expect vector $0000 then return to $%04X) ===\n",
           rst_pc, halt_pc);
    printf("sysclk  PC     ADDR   IR   DI   DO   SP     MC  TS  RD WR notes\n");
    printf("------  ----   ----   ---  ---  ---  ----   --  --  -- -- ----------------\n");

    uint16_t last_pc = 0xFFFF;
    uint16_t last_addr = 0xFFFF;
    uint16_t last_sp = 0xFFFF;
    uint8_t last_ir = 0xFF;
    uint8_t last_mcycle = 0;
    uint8_t last_tstate = 0;

    uint16_t initial_sp = dut->dbg_cpu_sp;

    bool noted_halt_fetch = false;
    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);
        if (dut->dbg_boot_rom_enabled) continue;

        uint16_t pc_reg = dut->dbg_cpu_pc;
        uint16_t addr = dut->dbg_cpu_addr;
        uint16_t sp = dut->dbg_cpu_sp;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t di = dut->dbg_cpu_di;
        uint8_t dout = dut->dbg_cpu_do;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        bool rd_n = dut->dbg_cpu_rd_n;
        bool wr_n = dut->dbg_cpu_wr_n;
        bool wr_edge = dut->dbg_cpu_wr_n_edge;

        bool write = dut->dbg_cpu_write;

        bool changed = (pc_reg != last_pc) || (addr != last_addr) || (sp != last_sp) ||
                       (ir != last_ir) || (mcycle != last_mcycle) || (tstate != last_tstate) ||
                       (wr_edge && write);

        bool in_window = (pc_reg >= 0x014C && pc_reg <= 0x0160) || (pc_reg <= 0x0010);
        bool stack_write = (wr_edge && write && addr >= 0xB000 && addr <= 0xD000);

        if (changed && (in_window || stack_write)) {
            printf("%6d  $%04X  $%04X  $%02X $%02X $%02X $%04X  %-2s %-2s  %d  %d ",
                   cycle, pc_reg, addr, ir, di, dout, sp,
                   decode_mcycle(mcycle), decode_tstate(tstate),
                   rd_n ? 1 : 0, wr_n ? 1 : 0);
            if (wr_edge && write) {
                printf("[WRITE $%04X <= $%02X] ", addr, dout);
            }
            printf("\n");
        }

        last_pc = pc_reg;
        last_addr = addr;
        last_sp = sp;
        last_ir = ir;
        last_mcycle = mcycle;
        last_tstate = tstate;

        if (pc_reg == halt_pc && !noted_halt_fetch) {
            printf("\nNote: sequential PC reached HALT at $%04X; waiting to see if RST overrides PC.\n\n",
                   halt_pc);
            noted_halt_fetch = true;
        }
    }

    printf("\nInitial SP=$%04X, Final SP=$%04X\n", initial_sp, dut->dbg_cpu_sp);
    printf("Stack bytes around $%04X:\n", (uint16_t)(initial_sp - 2));
    for (int i = -2; i < 4; i++) {
        uint16_t a = initial_sp + i;
        printf("  [$%04X] = $%02X\n", a, sdram->read8(a));
    }

    delete sdram;
    delete dut;
    return 0;
}
