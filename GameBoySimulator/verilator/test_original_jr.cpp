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

    rom[0x150] = 0xC3; rom[0x151] = 0x60; rom[0x152] = 0x01;  // JP $0160
    
    rom[0x160] = 0x18; rom[0x161] = 0x02;  // JR +2 (should jump to $0164)
    rom[0x162] = 0x76;  // HALT (should skip)
    rom[0x163] = 0x76;  // HALT (should skip)
    rom[0x164] = 0x00;  // NOP (target)
    rom[0x165] = 0x76;  // HALT (success marker)

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

    printf("Testing original TV80 JR behavior...\n\n");
    printf("Expected: JR +2 from $0160 should jump to $0164\n");
    printf("  $0160: JR opcode\n");
    printf("  $0161: Offset byte (+2)\n");
    printf("  $0162: HALT (skip)\n");
    printf("  $0163: HALT (skip)\n");
    printf("  $0164: NOP (target)\n\n");

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
        }

        if (boot_completed && pc >= 0x160 && pc <= 0x166 && pc != last_pc) {
            printf("  PC = $%04X", pc);
            if (pc == 0x160) printf(" (JR opcode)");
            else if (pc == 0x161) printf(" (offset)");
            else if (pc == 0x162) printf(" (HALT - should skip!)");
            else if (pc == 0x163) printf(" (HALT - should skip!)");
            else if (pc == 0x164) printf(" (NOP - target) ✅");
            else if (pc == 0x165) printf(" (HALT - success)");
            printf("\n");
            last_pc = pc;
            
            if (pc == 0x162 || pc == 0x163) {
                printf("\n❌ FAILURE: PC at $%04X instead of jumping to $0164\n", pc);
                return 1;
            }
            if (pc == 0x164) {
                printf("\n✅ SUCCESS: JR jumped correctly to $0164!\n");
                return 0;
            }
        }
    }

    printf("\n❌ TIMEOUT\n");
    return 1;
}
