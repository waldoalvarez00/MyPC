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
    memset(rom, 0x00, sizeof(rom));
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    const uint8_t offset = 0x02;
    const uint16_t jr_operand_pc = 0x0151;
    const uint16_t fallthrough_pc = jr_operand_pc + 2;  // PC after JR bytes
    const uint16_t target_pc = fallthrough_pc + (int8_t)offset;
    const uint16_t halt_pc = target_pc + 1;

    // At $0150: SCF; JR C,offset; two HALTs near fallthrough; NOP at target; HALT after.
    rom[0x150] = 0x37;                           // SCF (set carry)
    rom[jr_operand_pc] = 0x38;                  // JR C,r8
    rom[jr_operand_pc + 1] = offset;            // displacement
    rom[fallthrough_pc] = 0x76;                 // HALT (skip if jump works)
    rom[fallthrough_pc + 1] = 0x76;             // HALT (skip if jump works)
    if (target_pc < sizeof(rom)) rom[target_pc] = 0x00;  // NOP target
    if (halt_pc < sizeof(rom)) rom[halt_pc] = 0x76;      // HALT success

    setup_system(dut, sdram, rom, sizeof(rom));

    printf("\n=== Taken JR C Trace (offset %+d, expect jump to $%04X) ===\n",
           (int8_t)offset, target_pc);
    printf("sysclk  PC     IR   DI   F    MCd MC  TS  RD_n clken notes\n");
    printf("------  ----   ---  ---  ---  --- --  --  ---- ----- ----------------\n");

    uint16_t last_pc = 0xFFFF;
    uint8_t last_ir = 0xFF;
    uint8_t last_mcycle = 0;
    uint8_t last_tstate = 0;
    int printed = 0;

    for (int cycle = 0; cycle < 600000; cycle++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_boot_rom_enabled) continue;

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t di = dut->dbg_cpu_di;
        uint8_t f = dut->dbg_cpu_f;
        uint8_t mcd = dut->dbg_cpu_mcycles_d;
        uint8_t mc = dut->dbg_cpu_mcycles;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        bool rd_n = dut->dbg_cpu_rd_n;
        bool clken = dut->dbg_cpu_clken;

        bool state_changed = (pc != last_pc) || (ir != last_ir) || (mcycle != last_mcycle) || (tstate != last_tstate);
        if (state_changed && pc >= 0x014E && pc <= 0x0160) {
            printf("%6d  $%04X  $%02X $%02X $%02X   %d   %d  %-2s  %-2s    %d     %d    ",
                   cycle, pc, ir, di, f, mcd, mc, decode_mcycle(mcycle), decode_tstate(tstate),
                   rd_n ? 1 : 0, clken ? 1 : 0);
            if (pc != last_pc) printf("[PC change] ");
            if (ir != last_ir) printf("[IR %02X→%02X] ", last_ir, ir);
            printf("\n");
            printed++;
        }

        last_pc = pc;
        last_ir = ir;
        last_mcycle = mcycle;
        last_tstate = tstate;

        if (pc == halt_pc) {
            printf("\n✅ Reached HALT at $%04X (jump taken)\n", halt_pc);
            break;
        }
        if (printed > 200) break;
    }

    uint16_t final_pc = dut->dbg_cpu_pc;
    if (final_pc != halt_pc) {
        printf("\n❌ Final PC=$%04X (expected $%04X)\n", final_pc, halt_pc);
    }

    delete sdram;
    delete dut;
    return 0;
}
