// Focused debug test for JR NC instruction timing
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Simple test: set C=0 via clearing flags, then JR NC should jump
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // HALT everywhere

    // Entry point at $0100
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // Test sequence at $0150:
    // AND A - clears carry (also sets Z=1 for A=0, but we test NC)
    // JR NC, +2 - should jump (C=0)
    // HALT - should be skipped
    // NOP - success marker
    // HALT
    rom[0x150] = 0xA7;                // AND A (clears C flag, sets Z)
    rom[0x151] = 0x30; rom[0x152] = 0x01;  // JR NC, +1 (skip 1 byte)
    rom[0x153] = 0x76;                // HALT (should skip)
    rom[0x154] = 0x00;                // NOP (success)
    rom[0x155] = 0x76;                // HALT

    sdram->loadBinary(0, rom, sizeof(rom));

    // Boot ROM - setup and jump to cartridge
    // Note: Boot ROM disable will be done by cartridge code at $0100
    uint8_t boot[256];
    memset(boot, 0, 256);
    int bp = 0;
    // LD SP, $FFFE
    boot[bp++] = 0x31; boot[bp++] = 0xFE; boot[bp++] = 0xFF;
    // Enable LCD (LCDC = 0x91)
    boot[bp++] = 0x3E; boot[bp++] = 0x91;
    boot[bp++] = 0xE0; boot[bp++] = 0x40;
    // Jump to $0100 (boot ROM stays enabled, but $0100+ is cartridge anyway)
    boot[bp++] = 0xC3; boot[bp++] = 0x00; boot[bp++] = 0x01;

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Upload boot ROM
    dut->boot_download = 1;
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

    // Initialize cart
    dut->ioctl_addr = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);
    for (int w = 0; w < 5000 && !dut->dbg_cart_ready; w++) {
        tick_with_sdram(dut, sdram);
    }

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("Testing JR NC with detailed debug...\n\n");

    bool boot_done = false;
    bool tracing = false;
    int trace_count = 0;
    uint16_t last_pc = 0xFFFF;
    uint8_t last_mcycle = 0xFF;

    for (int cycle = 0; cycle < 500000 && trace_count < 3000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t f = dut->dbg_cpu_f;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t mcycles = dut->dbg_cpu_mcycles;
        uint8_t mcycles_d = dut->dbg_cpu_mcycles_d;
        bool jump_e = dut->dbg_cpu_jump_e;
        bool inc_pc = dut->dbg_cpu_inc_pc;
        bool no_read = dut->dbg_cpu_no_read;
        bool last_mc = dut->dbg_cpu_last_mcycle;

        // Boot is done when PC reaches $0100 (cartridge entry point)
        if (!boot_done) {
            if (pc >= 0x100) {
                boot_done = true;
                printf("Boot complete at cycle %d, PC=%04X, entering test code...\n", cycle, pc);
            } else if (cycle % 50000 == 0) {
                printf("Waiting for boot... cycle=%d PC=%04X boot_rom_enabled=%d\n",
                       cycle, pc, dut->dbg_boot_rom_enabled);
            }
        }

        // Trace when we're near the JR NC instruction (extended range)
        if (boot_done && pc >= 0x100 && pc <= 0x160) {
            if (!tracing) {
                printf("\nDetailed trace at JR NC:\n");
                printf("cycle   PC    IR   F    mcycle   tstate  mcycles mcycles_d JumpE Inc_PC NoRead LastMC\n");
                printf("---------------------------------------------------------------------------------------\n");
                tracing = true;
            }

            // Print every cycle while in this region
            printf("%6d  %04X  %02X   %02X   %02X       %02X      %d       %d         %d     %d      %d      %d\n",
                   cycle, pc, ir, f, mcycle, tstate, mcycles, mcycles_d, jump_e, inc_pc, no_read, last_mc);
            trace_count++;

            // Check success/failure
            if (pc == 0x154 && ir == 0x00) {
                printf("\n✅ JR NC PASSED - jumped to NOP at $0154\n");
                break;
            }
            if (pc == 0x153 && ir == 0x76) {
                printf("\n❌ JR NC FAILED - fell through to HALT at $0153\n");
                break;
            }
        }

        // Timeout check
        if (cycle > 400000 && !tracing) {
            printf("Test taking too long, PC=%04X\n", pc);
            break;
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
