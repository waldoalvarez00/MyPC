#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== LCD State Throughout Boot ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
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

    printf("Monitoring LCDC and LCD state changes...\n\n");

    uint8_t last_lcdc = 0;
    bool last_lcd_on = false;
    int lcd_on_cycle = -1;
    int lcd_off_cycle = -1;

    for (int i = 0; i < 30000; i++) {
        uint8_t lcdc = dut->dbg_lcdc;
        bool lcd_on = dut->dbg_lcd_on;

        if (lcdc != last_lcdc) {
            printf("  [%6d] LCDC changed: $%02X -> $%02X (bit7=%d)\n",
                   i, last_lcdc, lcdc, (lcdc >> 7) & 1);
            last_lcdc = lcdc;
        }

        if (lcd_on != last_lcd_on) {
            if (lcd_on) {
                lcd_on_cycle = i;
                printf("  [%6d] *** LCD TURNED ON *** (LCDC=$%02X)\n", i, lcdc);
            } else {
                lcd_off_cycle = i;
                printf("  [%6d] *** LCD TURNED OFF *** (LCDC=$%02X)\n", i, lcdc);
            }
            last_lcd_on = lcd_on;
        }

        tick_with_sdram(dut, sdram);

        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  [%6d] Boot ROM disabled\n", i);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("LCD turned on: %s", lcd_on_cycle >= 0 ? "YES" : "NO");
    if (lcd_on_cycle >= 0) printf(" (cycle %d)", lcd_on_cycle);
    printf("\n");
    
    printf("LCD turned off: %s", lcd_off_cycle >= 0 ? "YES" : "NO");
    if (lcd_off_cycle >= 0) printf(" (cycle %d)", lcd_off_cycle);
    printf("\n");
    
    printf("Final LCD state: %s\n", dut->dbg_lcd_on ? "ON" : "OFF");
    printf("Final LCDC: $%02X\n", dut->dbg_lcdc);

    delete sdram;
    delete dut;
    return 0;
}
