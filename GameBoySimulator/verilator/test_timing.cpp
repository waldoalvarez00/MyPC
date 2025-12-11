#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== Timing Test - Sample BEFORE tick ===\n\n");

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

    printf("Monitoring - sampling EVERY cycle around $FF40 write...\n\n");

    for (int i = 0; i < 15000; i++) {
        // Sample BEFORE tick
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;
        uint8_t data = dut->dbg_cpu_do;
        bool sel_reg = dut->dbg_video_cpu_sel_reg;
        bool cpu_wr = dut->dbg_video_cpu_wr;
        uint8_t lcdc = dut->dbg_lcdc;

        // Look for writes to $FF40-$FF4F
        if (addr >= 0xFF40 && addr <= 0xFF4F && wr_n == 0) {
            printf("  [%6d] BEFORE tick: addr=$%04X wr_n=%d edge=%d data=$%02X sel_reg=%d cpu_wr=%d lcdc=$%02X\n",
                   i, addr, wr_n, wr_edge, data, sel_reg, cpu_wr, lcdc);
        }

        tick_with_sdram(dut, sdram);

        // Sample AFTER tick
        if (addr >= 0xFF40 && addr <= 0xFF4F && wr_n == 0) {
            printf("  [%6d] AFTER  tick: addr=$%04X wr_n=%d edge=%d data=$%02X sel_reg=%d cpu_wr=%d lcdc=$%02X\n",
                   i, dut->dbg_cpu_addr, dut->dbg_cpu_wr_n, dut->dbg_cpu_wr_n_edge, 
                   dut->dbg_cpu_do, dut->dbg_video_cpu_sel_reg, dut->dbg_video_cpu_wr, dut->dbg_lcdc);
            
            if (addr == 0xFF40) {
                printf("\n  Found $FF40 write! Stopping to analyze.\n");
                printf("    cpu_wr_n_edge = %d\n", wr_edge);
                printf("    !cpu_wr_n_edge should be %d\n", !wr_edge);
                printf("    but cpu_wr = %d\n\n", cpu_wr);
                break;
            }
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
