#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Video Module Inputs Test ===\n\n");

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

    printf("Monitoring video module inputs during $FF40 write...\n\n");

    for (int i = 0; i < 15000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;

        tick_with_sdram(dut, sdram);

        // Look for any access to $FF40
        if (addr == 0xFF40 && wr_edge == 0 && wr_n == 0) {
            uint8_t data = dut->dbg_cpu_do;
            uint8_t lcdc_before = dut->dbg_lcdc;
            bool sel_reg = dut->dbg_video_cpu_sel_reg;
            bool cpu_wr = dut->dbg_video_cpu_wr;
            
            printf("  [%6d] Write to $FF40 detected!\n", i);
            printf("    CPU signals:\n");
            printf("      addr = $%04X\n", addr);
            printf("      data = $%02X\n", data);
            printf("      wr_n = %d, edge = %d\n", wr_n, wr_edge);
            printf("\n    Video module inputs:\n");
            printf("      cpu_sel_reg = %d %s\n", sel_reg, sel_reg ? "(GOOD)" : "(BAD - should be 1!)");
            printf("      cpu_wr = %d %s\n", cpu_wr, cpu_wr ? "(GOOD)" : "(BAD - should be 1!)");
            printf("      lcdc_before = $%02X\n", lcdc_before);
            
            // Check several cycles
            printf("\n    Checking next few cycles:\n");
            for (int j = 1; j <= 5; j++) {
                tick_with_sdram(dut, sdram);
                printf("      [+%d] lcdc=$%02X sel_reg=%d cpu_wr=%d\n",
                       j, dut->dbg_lcdc, dut->dbg_video_cpu_sel_reg, dut->dbg_video_cpu_wr);
            }
            
            printf("\n    Result: LCDC = $%02X %s\n", dut->dbg_lcdc,
                   dut->dbg_lcdc == 0x91 ? "(SUCCESS!)" : "(FAILED - should be $91)");
            
            if (dut->dbg_lcdc != 0x91) {
                if (!sel_reg || !cpu_wr) {
                    printf("\n✗ Input signals not correct - video module never saw the write!\n");
                } else {
                    printf("\n✗ Inputs correct but register didn't update - always block problem!\n");
                }
            }
            
            break;
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
