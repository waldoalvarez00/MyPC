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

    printf("=== VRAM Logo Verification ===\n\n");

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

    printf("Running until boot ROM completes...\n");

    // Run until boot ROM disables
    bool boot_completed = false;
    for (int i = 0; i < 50000; i++) {
        tick_with_sdram(dut, sdram);
        if (!dut->dbg_boot_rom_enabled) {
            boot_completed = true;
            printf("  Boot ROM disabled at cycle %d\n\n", i);
            break;
        }
    }

    if (!boot_completed) {
        printf("ERROR: Boot ROM did not complete\n");
        delete sdram;
        delete dut;
        return 1;
    }

    // Check VRAM contents - Nintendo logo should be at $8010-$808F
    printf("Checking VRAM contents (logo should be at $8010-$808F):\n");
    
    // Read from SDRAM model - VRAM is mapped starting at some offset
    // Let's check if any data was written
    bool vram_has_data = false;
    
    // Sample some addresses
    printf("\nSample VRAM contents:\n");
    for (int addr = 0x8010; addr <= 0x808F; addr += 16) {
        printf("  $%04X:", addr);
        for (int i = 0; i < 16 && (addr + i) <= 0x808F; i++) {
            // Try reading through CPU
            dut->dbg_force_cpu_addr = addr + i;
            dut->dbg_force_cpu_read = 1;
            tick_with_sdram(dut, sdram);
            uint8_t val = dut->dbg_cpu_data_in & 0xFF;
            printf(" %02X", val);
            if (val != 0) vram_has_data = true;
        }
        printf("\n");
    }
    dut->dbg_force_cpu_read = 0;

    printf("\n--- Results ---\n");
    printf("Boot ROM completed: %s\n", boot_completed ? "YES" : "NO");
    printf("VRAM contains data: %s\n", vram_has_data ? "YES" : "NO");
    printf("LCD enabled: %s\n", dut->dbg_lcd_on ? "YES" : "NO");

    delete sdram;
    delete dut;
    return 0;
}
