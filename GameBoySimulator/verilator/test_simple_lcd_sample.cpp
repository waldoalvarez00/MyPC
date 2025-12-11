// Simple test - just sample lcd_data_gb every cycle and see what we get
#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Simple LCD Sampling Test ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

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

    printf("Running boot ROM for 1M cycles...\n");
    run_cycles_with_sdram(dut, sdram, 1000000);

    printf("\nSampling lcd_data_gb every 1000 cycles for 100K cycles...\n");

    int counts[4] = {0, 0, 0, 0};
    int total_samples = 0;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        if (i % 1000 == 0) {
            uint8_t val = dut->dbg_lcd_data_gb;
            if (val < 4) {
                counts[val]++;
                total_samples++;
            }
        }
    }

    printf("\nSampled %d times\n", total_samples);
    printf("\nPixel value distribution:\n");
    printf("  Color 0 (white):     %d samples (%.1f%%)\n", counts[0], 100.0 * counts[0] / total_samples);
    printf("  Color 1 (lt gray):   %d samples (%.1f%%)\n", counts[1], 100.0 * counts[1] / total_samples);
    printf("  Color 2 (dk gray):   %d samples (%.1f%%)\n", counts[2], 100.0 * counts[2] / total_samples);
    printf("  Color 3 (black):     %d samples (%.1f%%)\n", counts[3], 100.0 * counts[3] / total_samples);

    printf("\n=== Diagnosis ===\n");
    if (counts[3] == total_samples) {
        printf("❌ ALL samples are BLACK (3)\n");
        printf("   This means VRAM is reading as 0xFF everywhere\n");
        printf("   Windows Verilator randomization is overriding initialization!\n");
    } else if (counts[0] == total_samples) {
        printf("✅ ALL samples are WHITE (0)\n");
        printf("   VRAM initialized to 0x00 successfully\n");
        printf("   But boot ROM tile data not visible\n");
    } else {
        printf("✅ MIXED values detected!\n");
        printf("   VRAM contains actual graphics data\n");
    }

    delete sdram;
    delete dut;

    return 0;
}
