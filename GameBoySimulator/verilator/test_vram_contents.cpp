// Test to read VRAM contents after boot ROM execution
// Purpose: Verify if boot ROM writes are actually persisting in VRAM

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== VRAM Contents After Boot ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

    // Load DMG boot ROM
    uint8_t dmg_boot[256];
    FILE* f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("ERROR: Cannot open dmg_boot.bin\n");
        return 1;
    }
    fread(dmg_boot, 1, 256, f);
    fclose(f);

    // Reset and download boot ROM
    reset_dut_with_sdram(dut, sdram, 100);

    dut->boot_download = 1;
    tick_with_sdram(dut, sdram);

    for (size_t addr = 0; addr < 256; addr += 2) {
        uint16_t word = dmg_boot[addr];
        if (addr + 1 < 256) {
            word |= (dmg_boot[addr + 1] << 8);
        }

        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }

        dut->boot_wr = 0;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
    }

    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    // Load minimal cart
    uint8_t cart[0x150];
    memset(cart, 0, sizeof(cart));
    cart[0x100] = 0x18;
    cart[0x101] = 0xFE;

    const uint8_t logo[] = {
        0xCE,0xED,0x66,0x66,0xCC,0x0D,0x00,0x0B,0x03,0x73,0x00,0x83,0x00,0x0C,0x00,0x0D,
        0x00,0x08,0x11,0x1F,0x88,0x89,0x00,0x0E,0xDC,0xCC,0x6E,0xE6,0xDD,0xDD,0xD9,0x99,
        0xBB,0xBB,0x67,0x63,0x6E,0x0E,0xEC,0xCC,0xDD,0xDC,0x99,0x9F,0xBB,0xB9,0x33,0x3E
    };
    memcpy(&cart[0x104], logo, sizeof(logo));

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    tick_with_sdram(dut, sdram);

    for (size_t i = 0; i < sizeof(cart); i++) {
        dut->ioctl_addr = i;
        dut->ioctl_dout = cart[i];
        dut->ioctl_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->ioctl_wr = 0;
    }

    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 10);

    printf("Running boot ROM for 500K cycles...\n");
    run_cycles_with_sdram(dut, sdram, 500000);

    // Now try to read VRAM contents directly
    // VRAM should be at addresses $8000-$9FFF in GameBoy memory space
    printf("\n=== VRAM Contents (first 256 bytes) ===\n");

    // We need to access VRAM through the internal structure
    // This is tricky since we can't directly read VRAM from outside
    // Instead, let's check what lcd_data_gb shows during rendering

    printf("\nMonitoring LCD output for 1 frame...\n");

    uint8_t pixel_values[160 * 144];
    int pixel_idx = 0;
    int last_mode = -1;
    int lines_captured = 0;

    for (int i = 0; i < 100000 && lines_captured < 10; i++) {
        tick_with_sdram(dut, sdram);

        uint8_t mode = dut->dbg_lcd_mode;

        // Mode 3 is pixel transfer - capture pixels
        if (mode == 3) {
            if (last_mode != 3 && pixel_idx < (int)sizeof(pixel_values)) {
                // Just entered mode 3 - start of scanline
            }

            if (dut->dbg_lcd_clkena && pixel_idx < (int)sizeof(pixel_values)) {
                pixel_values[pixel_idx++] = dut->dbg_lcd_data_gb;
            }
        } else if (last_mode == 3 && mode != 3) {
            // Just exited mode 3 - end of scanline
            lines_captured++;
        }

        last_mode = mode;
    }

    printf("Captured %d pixels from %d lines\n", pixel_idx, lines_captured);

    // Count pixel values
    int counts[4] = {0, 0, 0, 0};
    for (int i = 0; i < pixel_idx; i++) {
        if (pixel_values[i] < 4) {
            counts[pixel_values[i]]++;
        }
    }

    printf("\nPixel value distribution:\n");
    printf("  Color 0 (white):     %d pixels (%.1f%%)\n", counts[0], 100.0 * counts[0] / pixel_idx);
    printf("  Color 1 (lt gray):   %d pixels (%.1f%%)\n", counts[1], 100.0 * counts[1] / pixel_idx);
    printf("  Color 2 (dk gray):   %d pixels (%.1f%%)\n", counts[2], 100.0 * counts[2] / pixel_idx);
    printf("  Color 3 (black):     %d pixels (%.1f%%)\n", counts[3], 100.0 * counts[3] / pixel_idx);

    printf("\nFirst 100 pixels:\n");
    for (int i = 0; i < 100 && i < pixel_idx; i++) {
        printf("%d", pixel_values[i]);
        if ((i + 1) % 20 == 0) printf("\n");
    }
    printf("\n");

    printf("\n=== Diagnosis ===\n");
    if (counts[3] == pixel_idx) {
        printf("❌ ALL pixels are BLACK (3) - VRAM likely still 0xFF\n");
        printf("   Boot ROM writes may not be persisting!\n");
    } else if (counts[0] == pixel_idx) {
        printf("✅ ALL pixels are WHITE (0) - VRAM initialized to 0x00\n");
        printf("   Boot ROM hasn't written tile data yet, or tiles are blank\n");
    } else if (counts[0] > 0 || counts[1] > 0 || counts[2] > 0) {
        printf("✅ MIXED pixel values - VRAM contains data!\n");
        printf("   Boot ROM graphics should be visible\n");
    }

    delete sdram;
    delete dut;

    return 0;
}
