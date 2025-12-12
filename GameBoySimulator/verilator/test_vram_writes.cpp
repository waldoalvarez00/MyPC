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

    printf("=== Monitoring VRAM Writes During Boot ===\n\n");

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

    printf("Monitoring VRAM writes (addresses $8000-$9FFF)...\n\n");

    int vram_write_count = 0;
    uint16_t first_vram_addr = 0;
    uint16_t last_vram_addr = 0;

    for (int i = 0; i < 30000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        bool vram_wren = dut->dbg_vram_wren;

        tick_with_sdram(dut, sdram);

        // Detect VRAM writes
        if (vram_wren && addr >= 0x8000 && addr < 0xA000) {
            vram_write_count++;
            if (vram_write_count == 1) {
                first_vram_addr = addr;
                printf("  First VRAM write: addr=$%04X\n", addr);
            }
            last_vram_addr = addr;
            
            // Show first 10 writes
            if (vram_write_count <= 10) {
                printf("  VRAM write #%d: addr=$%04X\n", vram_write_count, addr);
            }
        }

        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  Boot ROM disabled at cycle %d\n", i);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("Total VRAM writes: %d\n", vram_write_count);
    if (vram_write_count > 0) {
        printf("First write: $%04X\n", first_vram_addr);
        printf("Last write: $%04X\n", last_vram_addr);
        printf("Expected: $8010-$808F (logo data)\n");
        
        if (first_vram_addr == 0x8010) {
            printf("\n✓ Logo writes started at correct address!\n");
        } else {
            printf("\n✗ Unexpected first address (expected $8010)\n");
        }
    } else {
        printf("\n✗ ERROR: No VRAM writes detected!\n");
        printf("  The boot ROM should copy the logo to VRAM.\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
