#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

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

int main() {
    printf("\n=== SDRAM Wait Counter Analysis ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;
    rom[0x150] = 0x18; rom[0x151] = 0x02;
    rom[0x152] = 0x76;

    setup_system(dut, sdram, rom, sizeof(rom));

    bool in_region = false;
    int trace_count = 0;
    uint16_t last_pc = 0xFFFF;

    printf("Monitoring first 50 cycles after PC reaches $0150:\n");
    printf("Cycle    PC     ce  sdram_wait  Notes\n");
    printf("---------------------------------------\n");

    for (int cycle = 0; cycle < 50000; cycle++) {
        // Check signals BEFORE tick
        uint16_t pc = dut->dbg_cpu_addr;
        
        tick_with_sdram(dut, sdram);

        if (!dut->dbg_boot_rom_enabled && pc >= 0x0150 && pc <= 0x0152) {
            if (!in_region || pc != last_pc) {
                in_region = true;
                last_pc = pc;
            }

            if (trace_count < 50) {
                printf("%6d  $%04X  %d   ?           ", 
                       cycle, pc, dut->ce ? 1 : 0);
                
                if (pc == 0x0150 && trace_count == 0) {
                    printf("PC arrived at JR instruction");
                }
                printf("\n");
                trace_count++;
            }

            if (trace_count >= 50) break;
        }
    }

    printf("\nNote: 'ce' is clock enable (should pulse every 8 cycles)\n");
    printf("Wait counter should decrement every system clock, not every ce pulse\n\n");

    delete sdram;
    delete dut;
    return 0;
}
