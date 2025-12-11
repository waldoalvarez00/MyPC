#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== Comprehensive Diagnostic ===\n\n");

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

    printf("Scanning for $FF40 write...\n\n");

    for (int i = 0; i < 15000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        
        // Detect the exact cycle of write
        if (addr == 0xFF40 && dut->dbg_cpu_wr_n == 0 && dut->dbg_cpu_wr_n_edge == 0) {
            printf("FOUND! Cycle %d\n\n", i);
            printf("=== Before Clock Tick ===\n");
            printf("  reset = %d\n", dut->reset);
            printf("  addr = $%04X\n", addr);
            printf("  cpu_do = $%02X\n", dut->dbg_cpu_do);
            printf("  cpu_wr_n = %d\n", dut->dbg_cpu_wr_n);
            printf("  cpu_wr_n_edge = %d\n", dut->dbg_cpu_wr_n_edge);
            printf("  video.cpu_sel_reg = %d\n", dut->dbg_video_cpu_sel_reg);
            printf("  video.cpu_wr = %d\n", dut->dbg_video_cpu_wr);
            printf("  LCDC = $%02X\n", dut->dbg_lcdc);
            printf("\n");
            
            // Now do the clock tick and see what happens
            printf("=== Executing Clock Tick ===\n");
            tick_with_sdram(dut, sdram);
            
            printf("\n=== After Clock Tick ===\n");
            printf("  LCDC = $%02X  %s\n", dut->dbg_lcdc,
                   dut->dbg_lcdc == 0x91 ? "SUCCESS!" : "FAILED!");
            printf("  lcd_on = %d\n", dut->dbg_lcd_on);
            
            if (dut->dbg_lcdc != 0x91) {
                printf("\n✗✗✗ CRITICAL BUG ✗✗✗\n");
                printf("All conditions met but register didn't update!\n");
                printf("  - cpu_sel_reg = 1 ✓\n");
                printf("  - cpu_wr was 1 ✓\n");
                printf("  - addr = $40 ✓\n");
                printf("  - data = $91 ✓\n");
                printf("  - reset = 0 ✓\n");
                printf("  - But LCDC stayed at $%02X!\n", dut->dbg_lcdc);
                printf("\nThis suggests a Verilator synthesis or simulation bug.\n");
            }
            break;
        }
        
        tick_with_sdram(dut, sdram);
    }

    delete sdram;
    delete dut;
    return 0;
}
