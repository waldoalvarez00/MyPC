#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;

    // Test JR C when carry is CLEAR (condition FALSE)
    rom[0x150] = 0x3F;  // CCF - complement carry (clears it if initially 0)
    rom[0x151] = 0x38; rom[0x152] = 0x05;  // JR C, +5 (should NOT jump)
    rom[0x153] = 0x00;  // NOP (should execute)
    rom[0x154] = 0x00;  // NOP (should execute)
    rom[0x155] = 0x76;  // HALT (success - condition was false, didn't jump)

    // Target if it jumped (wrong):
    rom[0x158] = 0x76;  // HALT (failure - jumped when it shouldn't)

    sdram->loadBinary(0, rom, sizeof(rom));

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

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;

    printf("Testing JR C when carry is CLEAR (condition FALSE)...\n\n");
    printf("Expected: JR C should NOT jump, execute NOPs at $0153-$0154, halt at $0155\n\n");

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
        }

        if (boot_completed && pc >= 0x150 && pc <= 0x159 && pc != last_pc) {
            printf("  PC = $%04X", pc);
            if (pc == 0x150) printf(" (CCF)");
            else if (pc == 0x151) printf(" (JR C)");
            else if (pc == 0x153) printf(" (NOP - correct, didn't jump)");
            else if (pc == 0x154) printf(" (NOP - correct)");
            else if (pc == 0x155) {
                printf(" (HALT - ✅ SUCCESS: Condition was false, didn't jump)\n");
                return 0;
            }
            else if (pc == 0x158) {
                printf(" (HALT - ❌ FAILURE: Jumped when it shouldn't!)\n");
                return 1;
            }
            printf("\n");
            last_pc = pc;
        }
    }

    printf("❌ FAILURE: Timeout\n");
    return 1;
}
