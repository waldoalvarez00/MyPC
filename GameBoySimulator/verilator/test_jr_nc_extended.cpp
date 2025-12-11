#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    // Boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    rom[0x150] = 0x37;  // SCF
    rom[0x151] = 0x38; rom[0x152] = 0x02;  // JR C, +2
    rom[0x153] = 0x76;  // HALT (should skip)
    rom[0x154] = 0x3F;  // CCF
    rom[0x155] = 0x30; rom[0x156] = 0x02;  // JR NC, +2
    rom[0x157] = 0x76;  // HALT (should skip)
    rom[0x158] = 0x00;  // NOP (success)
    rom[0x159] = 0x76;  // HALT (end marker)

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
    int pc_count = 0;

    printf("Testing JR NC with extended trace...\n\n");

    for (int cycle = 0; cycle < 300000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
        }

        if (boot_completed && pc >= 0x150 && pc <= 0x15A && pc != last_pc) {
            printf("  PC = $%04X (IR=$%02X)\n", pc, ir);
            pc_count++;
            
            // Don't break, let it run to see all PCs
            if (pc_count > 20) {  // Safety limit
                printf("\n⚠️  Too many PC changes, stopping\n");
                break;
            }
            
            last_pc = pc;
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
