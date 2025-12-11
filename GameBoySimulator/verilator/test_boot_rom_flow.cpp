#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== Boot ROM Execution Flow Analysis ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);

    printf("Boot ROM key instruction sequences:\n");
    printf("  $0000: %02X %02X %02X       ; LD SP, $FFFE\n",
           boot_rom[0], boot_rom[1], boot_rom[2]);
    printf("  $0003: %02X %02X %02X       ; LD HL, $%02X%02X\n",
           boot_rom[3], boot_rom[4], boot_rom[5], boot_rom[5], boot_rom[4]);
    printf("  $0006: %02X                ; LD (HL+), A or something\n", boot_rom[6]);
    printf("  $0007: %02X %02X            ; BIT 5, H\n", boot_rom[7], boot_rom[8]);
    printf("  $0009: %02X %02X            ; JR Z, -5\n", boot_rom[9], boot_rom[10]);
    printf("\n");

    // Look for logo copy setup (LD DE, $0104 and LD HL, $8010)
    printf("Searching for Nintendo logo copy setup...\n");
    for (int i = 0; i < 250; i++) {
        // Look for "LD DE, nn" (opcode $11)
        if (boot_rom[i] == 0x11) {
            uint16_t de_val = boot_rom[i+1] | (boot_rom[i+2] << 8);
            printf("  $%04X: 11 %02X %02X       ; LD DE, $%04X\n",
                   i, boot_rom[i+1], boot_rom[i+2], de_val);
            if (de_val == 0x0104) {
                printf("         ^^^ This is Nintendo logo source address!\n");
            }
        }
        // Look for "LD HL, nn" (opcode $21)
        if (boot_rom[i] == 0x21) {
            uint16_t hl_val = boot_rom[i+1] | (boot_rom[i+2] << 8);
            if (hl_val == 0x8010) {
                printf("  $%04X: 21 %02X %02X       ; LD HL, $%04X\n",
                       i, boot_rom[i+1], boot_rom[i+2], hl_val);
                printf("         ^^^ This is Nintendo logo VRAM destination!\n");
            }
        }
    }
    printf("\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM
    dut->boot_download = 1;
    for (int i = 0; i < 256; i += 2) {
        dut->boot_addr = i;
        dut->boot_data = boot_rom[i] | (boot_rom[i+1] << 8);
        dut->boot_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;

    // Simulate cart with Nintendo logo at $0104
    printf("Setting up cart ROM with Nintendo logo...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;

    // Write Nintendo logo bytes at $0104-$0133
    // (Actual Nintendo logo - 48 bytes)
    uint8_t nintendo_logo[] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
    };

    for (int i = 0; i < 48; i += 2) {
        uint16_t addr = (0x0104 + i) >> 1;
        uint16_t data = nintendo_logo[i] | (nintendo_logo[i+1] << 8);
        dut->ioctl_addr = addr;
        dut->ioctl_dout = data;
        dut->ioctl_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->ioctl_wr = 0;
    }

    // Also write entry point at $0100
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;
    dut->ioctl_wr = 1;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    printf("✓ Cart ROM setup complete with Nintendo logo\n\n");

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Tracing execution to find logo copy...\n\n");

    uint16_t last_pc = 0;
    int logo_writes = 0;

    for (int i = 0; i < 30000; i++) {
        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;

        // Detect writes to logo VRAM area ($8010-$808F)
        if (addr >= 0x8010 && addr < 0x8090 && wr_n == 0 && wr_edge == 0) {
            logo_writes++;
            if (logo_writes <= 10 || logo_writes > 86) {
                printf("  [%6d] Logo write #%d: PC=$%04X addr=$%04X HL=$%04X\n",
                       i, logo_writes, pc, addr, hl);
            } else if (logo_writes == 11) {
                printf("  ... (skipping middle writes)\n");
            }
        }

        tick_with_sdram(dut, sdram);
        last_pc = pc;

        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  Boot ROM disabled at cycle %d\n", i);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("Logo VRAM writes (to $8010-$808F): %d\n", logo_writes);
    printf("Expected: 48 tiles × 2 bytes = 96 writes\n");

    if (logo_writes >= 90) {
        printf("\n✅ PASS: Logo copied successfully!\n");
    } else {
        printf("\n❌ FAIL: Logo not fully copied (%d/96 writes)\n", logo_writes);
    }

    delete sdram;
    delete dut;
    return 0;
}
