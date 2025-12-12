#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    // MisterSDRAMModel ctor takes size in MB (not bytes).
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Direct LCDC Register Test ===\n\n");

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

    printf("Monitoring LCDC register value and write to $FF40...\n\n");

    uint8_t last_wr_n = 1;
    bool found_write = false;

    for (int i = 0; i < 50000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;
        uint8_t data_out = dut->dbg_cpu_do;
        uint8_t lcdc_val = dut->dbg_lcdc;

        tick_with_sdram(dut, sdram);

        // Detect write to $FF40
        if (addr == 0xFF40 && wr_edge == 0 && last_wr_n == 1 && wr_n == 0) {
            found_write = true;
            printf("  [%6d] Write to $FF40 detected!\n", i);
            printf("           Data written: $%02X\n", data_out);
            printf("           LCDC before: $%02X\n", lcdc_val);
            
            // Check several cycles later
            for (int j = 1; j <= 20; j++) {
                tick_with_sdram(dut, sdram);
                uint8_t lcdc_after = dut->dbg_lcdc;
                bool lcd_on = dut->dbg_lcd_on;
                printf("           [+%2d] LCDC=$%02X lcd_on=%d\n", j, lcdc_after, lcd_on);
            }
            break;
        }

        last_wr_n = wr_n;

        if (!dut->dbg_boot_rom_enabled) break;
    }

    printf("\n--- Results ---\n");
    if (found_write) {
        uint8_t final_lcdc = dut->dbg_lcdc;
        printf("LCDC write detected: YES\n");
        printf("Final LCDC value: $%02X\n", final_lcdc);
        printf("Bit 7 (LCD enable): %d\n", (final_lcdc >> 7) & 1);
        printf("LCD ON signal: %s\n", dut->dbg_lcd_on ? "YES" : "NO");
        
        if ((final_lcdc & 0x80) && !dut->dbg_lcd_on) {
            printf("\n✗ BUG: LCDC bit 7 is set but lcd_on signal is not active!\n");
            printf("  Check lcd_on assignment in video module.\n");
        } else if (!(final_lcdc & 0x80)) {
            printf("\n✗ BUG: LCDC register did not update!\n");
            printf("  Write occurred but register stayed at $%02X\n", final_lcdc);
        } else {
            printf("\n✓ LCD enabled successfully!\n");
        }
    } else {
        printf("No write to $FF40 detected\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
