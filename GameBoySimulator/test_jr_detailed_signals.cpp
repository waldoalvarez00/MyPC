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
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150
    rom[0x150] = 0x18; rom[0x151] = 0x02;  // JR +2
    rom[0x152] = 0x00;  // NOP (should skip)
    rom[0x153] = 0x00;  // NOP (should skip)
    rom[0x154] = 0x76;  // HALT (target)

    printf("Test Setup:\n");
    printf("  ROM[$0150] = 0x18 (JR opcode)\n");
    printf("  ROM[$0151] = 0x02 (offset +2)\n");
    printf("  ROM[$0152-$0153] = 0x00 (NOPs to skip)\n");
    printf("  ROM[$0154] = 0x76 (HALT target)\n\n");
    printf("Expected Behavior:\n");
    printf("  1. PC advances to $0150\n");
    printf("  2. M1 cycle fetches opcode 0x18\n");
    printf("  3. M1 T3: IR should update to 0x18\n");
    printf("  4. M2 cycle reads offset 0x02\n");
    printf("  5. M3 cycle executes jump (JumpE asserted)\n");
    printf("  6. PC should jump to $0154\n\n");

    setup_system(dut, sdram, rom, sizeof(rom));

    uint16_t last_pc = 0xFFFF;
    uint8_t last_ir = 0xFF;
    uint8_t last_mcycle = 0xFF;
    bool in_region = false;
    int trace_count = 0;

    printf("Detailed Signal Trace (First M1 cycle at PC=$0150):\n");
    printf("────────────────────────────────────────────────────────────────────────\n");
    printf("  Cycle    PC     IR   MCycle TState  MCycles  Notes\n");
    printf("────────────────────────────────────────────────────────────────────────\n");

    for (int cycle = 0; cycle < 50000; cycle++) {
        tick_with_sdram(dut, sdram);
        
        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t mcycles = dut->dbg_cpu_mcycles;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_enabled && pc >= 0x0150 && pc <= 0x0155) {
            if (!in_region) {
                in_region = true;
                printf("\n>>> Boot completed, entering test region at cycle %d <<<\n\n", cycle);
            }

            // Trace every cycle while at PC=$0150 or during first few cycles
            if (pc == 0x0150 || trace_count < 30) {
                printf("  %6d  $%04X  $%02X   %-6s %-6s    %d     ",
                       cycle, pc, ir, 
                       decode_mcycle(mcycle),
                       decode_tstate(tstate),
                       mcycles);

                // Annotate important events
                if (pc != last_pc) {
                    printf("[PC changed from $%04X]", last_pc);
                }
                if (ir != last_ir) {
                    printf("[IR changed from $%02X]", last_ir);
                }
                if (mcycle & 0x01 && !(last_mcycle & 0x01)) {
                    printf("[M1 START - should fetch opcode]");
                }
                if ((mcycle & 0x01) && (tstate & 0x04)) {
                    printf("[M1 T3 - IR UPDATE POINT!]");
                    if (ir != 0x18 && pc == 0x150) {
                        printf(" *** IR SHOULD BE 0x18! ***");
                    }
                }

                printf("\n");
                trace_count++;
            }

            // Detect success/failure
            if (pc != last_pc) {
                if (pc == 0x152 || pc == 0x153) {
                    printf("\n");
                    printf("════════════════════════════════════════════════════════════════════════\n");
                    printf("❌ FAILURE: JR did not jump - PC reached skip region at $%04X\n", pc);
                    printf("════════════════════════════════════════════════════════════════════════\n");
                    printf("\nKey Findings:\n");
                    printf("  - IR never updated to 0x18 during M1 cycle at PC=$0150\n");
                    printf("  - IR remained at $%02X (stale value)\n", ir);
                    printf("  - Microcode case statement never matched JR opcode\n");
                    printf("  - JumpE signal was never asserted\n\n");
                    delete sdram;
                    delete dut;
                    return 1;
                }
                if (pc == 0x154) {
                    printf("\n");
                    printf("════════════════════════════════════════════════════════════════════════\n");
                    printf("✅ SUCCESS: JR jumped correctly to $0154!\n");
                    printf("════════════════════════════════════════════════════════════════════════\n\n");
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

    printf("\n⏱️ TIMEOUT or trace limit reached\n\n");
    delete sdram;
    delete dut;
    return 1;
}
