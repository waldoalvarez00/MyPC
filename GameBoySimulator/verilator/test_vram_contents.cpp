#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== VRAM Contents After Boot ROM ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("ERROR: Cannot load dmg_boot.bin\n");
        return 1;
    }
    fread(boot_rom, 1, 256, f);
    fclose(f);

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

    // Simulate cart
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Running boot ROM to completion...\n");

    // Run until boot ROM disables
    for (int i = 0; i < 30000; i++) {
        tick_with_sdram(dut, sdram);
        if (!dut->dbg_boot_rom_enabled) {
            printf("Boot ROM disabled at cycle %d\n\n", i);
            break;
        }
    }

    // Check video registers
    printf("Video Registers:\n");
    printf("  LCDC = $%02X\n", dut->dbg_lcdc);
    printf("    Bit 7 (LCD On): %d\n", (dut->dbg_lcdc >> 7) & 1);
    printf("    Bit 4 (BG Tile): %d\n", (dut->dbg_lcdc >> 4) & 1);
    printf("    Bit 3 (BG Map): %d\n", (dut->dbg_lcdc >> 3) & 1);
    printf("    Bit 0 (BG Enable): %d\n", dut->dbg_lcdc & 1);
    printf("  LCD ON signal: %d\n", dut->dbg_lcd_on);
    printf("  LCD Mode: %d\n", dut->dbg_lcd_mode);
    printf("\n");

    // Check LCD output signals
    printf("LCD Output Signals:\n");
    printf("  lcd_clkena: %d\n", dut->dbg_lcd_clkena);
    printf("  lcd_data: $%04X\n", dut->dbg_lcd_data);
    printf("  lcd_data_gb: %d\n", dut->dbg_lcd_data_gb);
    printf("\n");

    // Sample some VRAM locations where logo should be
    printf("Checking VRAM (logo should be at $8010-$808F):\n");
    
    // The boot ROM copies logo to VRAM starting at $8010
    // Let's check if any data was written there
    bool has_data = false;
    
    printf("First 16 bytes at $8010:\n  ");
    for (int i = 0; i < 16; i++) {
        // Access VRAM through SDRAM model
        uint16_t addr = 0x8010 + i;
        // VRAM in GameBoy maps to certain SDRAM addresses
        // For now, let's see if we can read anything
        printf("%02X ", 0); // Placeholder - need proper VRAM access
    }
    printf("\n");

    printf("\nNote: VRAM access through testbench is limited.\n");
    printf("      Need to check if video controller is reading VRAM correctly.\n");

    delete sdram;
    delete dut;
    return 0;
}
