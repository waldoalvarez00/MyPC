#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 0;  // ← ZERO LATENCY TEST

    printf("=== JR Test with CAS Latency = 0 ===\n\n");

    // Minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E;
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;
    minimal_boot[pc++] = 0x50;

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    rom[0x100] = 0xC3;  // JP $0160
    rom[0x101] = 0x60;
    rom[0x102] = 0x01;

    rom[0x160] = 0x18;  // JR +2
    rom[0x161] = 0x02;
    rom[0x162] = 0x76;  // HALT
    rom[0x163] = 0x00;  // NOP

    printf("CAS Latency: 0 (instant SDRAM access)\n");
    printf("Testing JR +2 at 0x0160\n\n");

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
    bool reached_163 = false;

    for (int cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;

        if (!boot_completed && !dut->dbg_boot_rom_enabled) {
            boot_completed = true;
            printf("Boot completed\n\n");
        }

        if (boot_completed && pc != last_pc) {
            if (pc >= 0x15F && pc <= 0x165) {
                printf("PC=$%04X", pc);
                if (pc == 0x160) printf(" (JR opcode)");
                else if (pc == 0x161) printf(" (JR offset)");
                else if (pc == 0x162) printf(" (HALT) ← BUG!");
                else if (pc == 0x163) {printf(" (target) ← SUCCESS!"); reached_163 = true; }
                printf("\n");
            }

            if (pc == 0x162) {
                printf("\n❌ JR FAILED even with CAS latency = 0\n");
                printf("   This is NOT a wait state issue!\n");
                printf("   This is a TV80 core bug or configuration issue.\n\n");
                break;
            }

            if (pc == 0x163) {
                printf("\n✅ JR WORKED with CAS latency = 0\n");
                printf("   This IS a wait state timing issue!\n");
                printf("   Wait state logic needs fix for 2-byte instructions.\n\n");
                break;
            }

            last_pc = pc;
        }
    }

    delete sdram;
    delete dut;
    return reached_163 ? 0 : 1;
}
