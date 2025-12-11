#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== LCD Output Test ===\n\n");

    // Load real game ROM
    FILE* f = fopen("game.gb", "rb");
    if (!f) {
        printf("ERROR: Could not open game.gb\n");
        return 1;
    }

    fseek(f, 0, SEEK_END);
    long rom_size = ftell(f);
    fseek(f, 0, SEEK_SET);

    uint8_t* rom = new uint8_t[rom_size];
    fread(rom, 1, rom_size, f);
    fclose(f);

    printf("ROM loaded: %ld bytes\n", rom_size);

    // Load into SDRAM
    sdram->loadBinary(0, rom, rom_size);

    // Create minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int boot_pc = 0;
    minimal_boot[boot_pc++] = 0xF3;  // DI

    // Pad with NOPs to 0xFC
    while (boot_pc < 0xFC) {
        minimal_boot[boot_pc++] = 0x00;  // NOP
    }

    // Boot ROM disable at end
    minimal_boot[boot_pc++] = 0x3E;  // LD A, $01
    minimal_boot[boot_pc++] = 0x01;
    minimal_boot[boot_pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[boot_pc++] = 0x50;

    printf("Boot ROM created: %d bytes\n", boot_pc);

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    // Upload boot ROM
    printf("Uploading boot ROM...\n");
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
    printf("Boot ROM uploaded\n");

    // Simulate cart download
    printf("Simulating cart download...\n");
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

    printf("\nRunning simulation to check LCD...\n\n");

    bool boot_completed = false;
    bool lcd_turned_on = false;
    int lcd_on_cycle = 0;
    bool vsync_seen = false;
    int first_vsync = 0;
    int non_gray_pixels = 0;
    int total_pixel_samples = 0;

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);

        // Check boot completion
        if (!boot_completed && !dut->dbg_boot_rom_enabled) {
            boot_completed = true;
            printf("[%6d] Boot ROM disabled\n", cycle);
        }

        // Check LCD on
        if (!lcd_turned_on && dut->dbg_lcd_on) {
            lcd_turned_on = true;
            lcd_on_cycle = cycle;
            printf("[%6d] LCD turned ON\n", cycle);
        }

        // Check VSync
        static uint8_t last_vs = 0;
        if (dut->VGA_VS && !last_vs) {
            if (!vsync_seen) {
                vsync_seen = true;
                first_vsync = cycle;
                printf("[%6d] First VSync detected\n", cycle);
            }
        }
        last_vs = dut->VGA_VS;

        // Sample pixel data
        if (lcd_turned_on && (cycle % 100 == 0)) {
            total_pixel_samples++;
            uint8_t r = dut->VGA_R;
            uint8_t g = dut->VGA_G;
            uint8_t b = dut->VGA_B;

            if (!((r == 0 && g == 0 && b == 0) ||
                  (r == 255 && g == 255 && b == 255))) {
                non_gray_pixels++;
            }
        }

        // Stop after first frame
        if (vsync_seen && (cycle - first_vsync) > 100000) {
            break;
        }
    }

    printf("\n=== Test Results ===\n");
    printf("Boot ROM completed: %s\n", boot_completed ? "YES" : "NO");
    printf("LCD turned on: %s", lcd_turned_on ? "YES" : "NO");
    if (lcd_turned_on) printf(" (cycle %d)", lcd_on_cycle);
    printf("\n");
    printf("VSync detected: %s", vsync_seen ? "YES" : "NO");
    if (vsync_seen) printf(" (first at cycle %d)", first_vsync);
    printf("\n");
    printf("Pixel samples: %d total, %d non-gray (%.1f%%)\n",
           total_pixel_samples, non_gray_pixels,
           total_pixel_samples > 0 ? 100.0 * non_gray_pixels / total_pixel_samples : 0);

    printf("\nFinal state:\n");
    printf("  dbg_lcd_on: %d\n", dut->dbg_lcd_on);
    printf("  dbg_lcd_clkena: %d\n", dut->dbg_lcd_clkena);
    printf("  dbg_lcd_mode: %d\n", dut->dbg_lcd_mode);
    printf("  VGA_R: %d, VGA_G: %d, VGA_B: %d\n", dut->VGA_R, dut->VGA_G, dut->VGA_B);

    delete[] rom;
    delete sdram;
    delete dut;

    if (!lcd_turned_on) {
        printf("\n❌ FAIL: LCD never turned on\n");
        return 1;
    }

    printf("\n✅ PASS: LCD operational\n");
    return 0;
}
