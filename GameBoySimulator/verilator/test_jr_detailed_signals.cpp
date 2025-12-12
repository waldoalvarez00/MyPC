#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>
#include <string.h>

void setup_system(Vtop* dut, MisterSDRAMModel* sdram, uint8_t* rom, size_t rom_size) {
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

const char* decode_mcycle(uint8_t mcycle) {
    if (mcycle & 0x01) return "M1";
    if (mcycle & 0x02) return "M2";
    if (mcycle & 0x04) return "M3";
    if (mcycle & 0x08) return "M4";
    if (mcycle & 0x10) return "M5";
    if (mcycle & 0x20) return "M6";
    if (mcycle & 0x40) return "M7";
    return "??";
}

const char* decode_tstate(uint8_t tstate) {
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
    printf("\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("   JR Instruction - Detailed MCycle/TState Signal Analysis\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;
    rom[0x150] = 0x18; rom[0x151] = 0x02;
    rom[0x152] = 0x00;
    rom[0x153] = 0x00;
    rom[0x154] = 0x76;

    printf("Test Setup:\n");
    printf("  ROM[$0150] = 0x18 (JR opcode)\n");
    printf("  ROM[$0151] = 0x02 (offset +2)\n\n");
    printf("Expected: M1 cycle at PC=$0150 should load IR with 0x18\n\n");

    setup_system(dut, sdram, rom, sizeof(rom));

    uint16_t last_pc = 0xFFFF;
    uint8_t last_ir = 0xFF;
    uint8_t last_mcycle = 0xFF;
    bool in_region = false;
    int trace_count = 0;

    printf("Signal Trace:\n");
    printf("──────────────────────────────────────────────────────────────────\n");
    printf("  Cycle    PC     IR   MCycle TState  Notes\n");
    printf("──────────────────────────────────────────────────────────────────\n");

    for (int cycle = 0; cycle < 50000; cycle++) {
        tick_with_sdram(dut, sdram);
        
        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_enabled && pc >= 0x0150 && pc <= 0x0155) {
            if (!in_region) {
                in_region = true;
            }

            if (pc == 0x0150 || trace_count < 30) {
                printf("  %6d  $%04X  $%02X   %-4s   %-4s   ",
                       cycle, pc, ir, 
                       decode_mcycle(mcycle),
                       decode_tstate(tstate));

                if (pc != last_pc) printf("[PC changed] ");
                if (ir != last_ir) printf("[IR: $%02X→$%02X] ", last_ir, ir);
                if ((mcycle & 0x01) && (tstate & 0x04)) {
                    printf("<<< M1 T3: IR UPDATE POINT >>>");
                    if (pc == 0x150 && ir != 0x18) {
                        printf(" *** SHOULD BE 0x18! ***");
                    }
                }

                printf("\n");
                trace_count++;
            }

            if (pc != last_pc) {
                if (pc == 0x152 || pc == 0x153) {
                    printf("\n❌ FAILURE: JR didn't jump (PC=$%04X, IR=$%02X)\n\n", pc, ir);
                    delete sdram;
                    delete dut;
                    return 1;
                }
                if (pc == 0x154) {
                    printf("\n✅ SUCCESS: JR jumped to $0154!\n\n");
                    delete sdram;
                    delete dut;
                    return 0;
                }
            }

            last_pc = pc;
            last_ir = ir;
            last_mcycle = mcycle;

            if (trace_count >= 100) break;
        }
    }

    printf("\n⏱️ TIMEOUT\n\n");
    delete sdram;
    delete dut;
    return 1;
}
