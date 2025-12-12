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

    printf("=== LCD Control Register (LCDC $FF40) Monitor ===\n\n");

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

    printf("Monitoring I/O writes (especially $FF40-$FF4F LCD registers)...\n\n");

    int io_write_count = 0;
    int lcdc_writes = 0;
    uint8_t last_wr_n = 1;

    for (int i = 0; i < 50000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;
        uint8_t data_out = dut->dbg_cpu_do;

        tick_with_sdram(dut, sdram);

        // Detect falling edge of wr_n to I/O region ($FF00-$FFFF)
        if (addr >= 0xFF00 && wr_edge == 0 && last_wr_n == 1 && wr_n == 0) {
            io_write_count++;
            
            // Focus on LCD registers ($FF40-$FF4F)
            if (addr >= 0xFF40 && addr <= 0xFF4F) {
                printf("  [%6d] I/O write #%d: $%04X = $%02X", 
                       i, io_write_count, addr, data_out);
                
                if (addr == 0xFF40) {
                    printf(" (LCDC - LCD Control)");
                    if (data_out & 0x80) printf(" *** LCD ON ***");
                    lcdc_writes++;
                } else if (addr == 0xFF41) {
                    printf(" (STAT - LCD Status)");
                } else if (addr == 0xFF42) {
                    printf(" (SCY - Scroll Y)");
                } else if (addr == 0xFF43) {
                    printf(" (SCX - Scroll X)");
                } else if (addr == 0xFF44) {
                    printf(" (LY - LCD Y)");
                } else if (addr == 0xFF45) {
                    printf(" (LYC - LY Compare)");
                } else if (addr == 0xFF47) {
                    printf(" (BGP - BG Palette)");
                } else if (addr == 0xFF48) {
                    printf(" (OBP0 - OBJ Palette 0)");
                } else if (addr == 0xFF49) {
                    printf(" (OBP1 - OBJ Palette 1)");
                } else if (addr == 0xFF4A) {
                    printf(" (WY - Window Y)");
                } else if (addr == 0xFF4B) {
                    printf(" (WX - Window X)");
                }
                
                printf("\n");
            }
        }

        last_wr_n = wr_n;

        // Stop after boot ROM disables
        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  [%6d] Boot ROM disabled\n", i);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("Total I/O writes: %d\n", io_write_count);
    printf("LCDC ($FF40) writes: %d\n", lcdc_writes);
    printf("LCD current state: %s\n", dut->dbg_lcd_on ? "ON" : "OFF");
    printf("Boot ROM completed: %s\n", !dut->dbg_boot_rom_enabled ? "YES" : "NO");

    delete sdram;
    delete dut;
    return 0;
}
