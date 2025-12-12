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

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // Vectors: RET at each RST target
    static const uint16_t vectors[8] = {0x0000,0x0008,0x0010,0x0018,0x0020,0x0028,0x0030,0x0038};
    for (int i = 0; i < 8; i++) rom[vectors[i]] = 0xC9;

    uint16_t pc = 0x150;
    rom[pc++] = 0x31; rom[pc++] = 0xFE; rom[pc++] = 0xFF;  // LD SP,$FFFE

    static const uint8_t rst_ops[8] = {0xC7,0xCF,0xD7,0xDF,0xE7,0xEF,0xF7,0xFF};
    uint16_t rst_sites[8];
    for (int i = 0; i < 8; i++) {
        rst_sites[i] = pc;
        rom[pc++] = rst_ops[i];
    }
    rom[pc++] = 0x76;  // HALT
    uint16_t halt_pc = pc - 1;

    setup_system(dut, sdram, rom, sizeof(rom));

    printf("\n=== RST Sweep Trace ===\n");
    printf("RST sites: ");
    for (int i = 0; i < 8; i++) printf("$%04X ", rst_sites[i]);
    printf("HALT at $%04X\n\n", halt_pc);

    bool seen_vec[8] = {false,false,false,false,false,false,false,false};
    uint16_t last_pc = 0xFFFF;
    int vec_hits = 0;

    for (int cycle = 0; cycle < 300000; cycle++) {
        tick_with_sdram(dut, sdram);
        if (dut->dbg_boot_rom_enabled) continue;

        uint16_t pc_reg = dut->dbg_cpu_pc;
        if (pc_reg != last_pc) {
            for (int i = 0; i < 8; i++) {
                if (pc_reg == vectors[i] && !seen_vec[i]) {
                    seen_vec[i] = true;
                    vec_hits++;
                    printf("Cycle %6d: Entered vector $%04X (RST %02X)\n",
                           cycle, vectors[i], rst_ops[i]);
                }
            }
            last_pc = pc_reg;
        }

        if (pc_reg == halt_pc) {
            printf("\n✅ Reached HALT at $%04X after all RSTs\n", halt_pc);
            break;
        }

        if (cycle == 299999) {
            printf("\n❌ Timeout. Final PC=$%04X SP=$%04X IR=$%02X\n",
                   pc_reg, dut->dbg_cpu_sp, dut->dbg_cpu_ir);
        }
    }

    printf("\nVectors seen:");
    for (int i = 0; i < 8; i++) {
        printf(" %04X=%d", vectors[i], seen_vec[i] ? 1 : 0);
    }
    printf("\n");

    delete sdram;
    delete dut;
    return 0;
}

