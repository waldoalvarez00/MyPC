#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    // Minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;  // LD A, 1
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;  // LDH (FF50), A

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    // Entry point
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // Test: Simple unconditional JR with markers before
    rom[0x150] = 0x00;  // NOP
    rom[0x151] = 0x00;  // NOP
    rom[0x152] = 0x18; rom[0x153] = 0x02;  // JR +2 (should jump to $0156)
    rom[0x154] = 0x76;  // HALT (should skip)
    rom[0x155] = 0x76;  // HALT (should skip)
    rom[0x156] = 0x00;  // NOP (target)
    rom[0x157] = 0x76;  // HALT (success)

    sdram->loadBinary(0, rom, sizeof(rom));

    // Reset
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    // Upload boot ROM
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

    // Trigger cart ready
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

    bool boot_completed = false;
    bool started_printing = false;
    int print_count = 0;
    const int MAX_PRINT = 200;  // Print max 200 cycles

    printf("=== Detailed IR Trace - Every Cycle ===\n");
    printf("Looking for PC=$0151-$0152 to see JR instruction fetch\n\n");

    for (int cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot completed at cycle %d\n\n", cycle);
        }

        // Start printing when we reach PC $0151 (NOP before JR)
        if (boot_completed && pc == 0x151 && !started_printing) {
            started_printing = true;
            printf("Started detailed trace at PC=$0151\n");
            printf("Format: Cycle PC IR MCycle TState\n\n");
        }

        // Print every cycle while in the region of interest
        if (started_printing && print_count < MAX_PRINT) {
            printf("%6d: PC=$%04X IR=$%02X M=%d T=%d\n",
                   cycle, pc, ir, mcycle, tstate);
            print_count++;

            // Check for key events
            if (pc == 0x152 && ir == 0x18) {
                printf("        ^^^ IR contains JR opcode (0x18)!\n");
            }
            if (pc == 0x154) {
                printf("\n❌ FAILURE: Reached $0154 (should skip) - JR did not jump\n");
                break;
            }
            if (pc == 0x156) {
                printf("\n✅ SUCCESS: Jumped to $0156!\n");
                break;
            }
        }

        if (print_count >= MAX_PRINT) {
            printf("\n⏱️ Reached print limit of %d cycles\n", MAX_PRINT);
            break;
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
