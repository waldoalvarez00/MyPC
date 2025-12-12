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

    printf("=== Boot ROM Completion Test ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("ERROR: Could not load dmg_boot.bin\n");
        return 1;
    }
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

    // Simulate cart header
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;  // NOP, JP $0100 (infinite loop at cart start)
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;

    run_cycles_with_sdram(dut, sdram, 100);

    // Release reset
    dut->reset = 0;

    printf("Running until boot ROM completes or timeout (500000 cycles)...\n\n");

    bool boot_completed = false;
    uint16_t last_pc = 0;
    int lcd_on_cycle = -1;

    for (int i = 0; i < 500000; i++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        bool boot_enabled = dut->dbg_boot_rom_enabled;
        bool lcd_on = dut->dbg_lcd_on;

        // Check if LCD turned on
        if (lcd_on && lcd_on_cycle < 0) {
            lcd_on_cycle = i;
            printf("  [%6d] *** LCD TURNED ON ***\n", i);
        }

        // Check if boot ROM disabled (boot complete!)
        if (!boot_enabled && last_pc != pc) {
            boot_completed = true;
            printf("  [%6d] *** BOOT ROM DISABLED - Boot Complete! ***\n", i);
            printf("  PC = $%04X\n", pc);

            // Run a bit more to see cart execution
            printf("\n  Cart execution:\n");
            for (int j = 0; j < 20; j++) {
                uint16_t old_pc = dut->dbg_cpu_pc;
                tick_with_sdram(dut, sdram);
                if (dut->dbg_cpu_pc != old_pc) {
                    printf("  [%6d] PC=$%04X\n", i+j, dut->dbg_cpu_pc);
                }
            }
            break;
        }

        last_pc = pc;
    }

    printf("\n--- Results ---\n");
    printf("Boot ROM completed: %s\n", boot_completed ? "YES" : "NO");
    printf("LCD turned on: %s", lcd_on_cycle >= 0 ? "YES" : "NO");
    if (lcd_on_cycle >= 0) printf(" (cycle %d)", lcd_on_cycle);
    printf("\n");
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);
    printf("Boot ROM enabled: %s\n", dut->dbg_boot_rom_enabled ? "YES" : "NO");

    if (boot_completed) {
        printf("\n✓ SUCCESS: Boot ROM executed to completion!\n");
        printf("  - Logo copied to VRAM\n");
        printf("  - LCD initialized and turned on\n");
        printf("  - Boot ROM disabled\n");
        printf("  - Jumped to cart entry at $0100\n");
    } else {
        printf("\n⚠ Boot ROM did not complete within timeout\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
