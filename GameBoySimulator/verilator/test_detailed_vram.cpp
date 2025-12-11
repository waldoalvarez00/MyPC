#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== Detailed VRAM Write Analysis ===\n\n");

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

    printf("Monitoring CPU writes to VRAM range ($8000-$9FFF)...\n");
    printf("Checking both cpu_wr_n and vram_wren signals.\n\n");

    int cpu_write_count = 0;
    int vram_wren_count = 0;

    for (int i = 0; i < 30000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;
        bool vram_wren = dut->dbg_vram_wren;

        // Check for CPU writes to VRAM range
        if (addr >= 0x8000 && addr < 0xA000 && wr_n == 0 && wr_edge == 0) {
            cpu_write_count++;
            if (cpu_write_count <= 20) {
                printf("  [%6d] CPU write #%d to $%04X (vram_wren=%d)\n",
                       i, cpu_write_count, addr, vram_wren);
            }
        }

        tick_with_sdram(dut, sdram);

        // Also count vram_wren assertions
        if (vram_wren) {
            vram_wren_count++;
        }

        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  Boot ROM disabled at cycle %d\n", i);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("CPU writes to VRAM range: %d\n", cpu_write_count);
    printf("vram_wren assertions: %d\n", vram_wren_count);
    
    if (cpu_write_count > 0 && vram_wren_count == 0) {
        printf("\n✗ BUG: CPU is writing to VRAM but vram_wren never asserts!\n");
        printf("  This means VRAM is not being written.\n");
    } else if (cpu_write_count == 0) {
        printf("\n✗ BUG: CPU never writes to VRAM range!\n");
        printf("  Boot ROM should copy logo data.\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
