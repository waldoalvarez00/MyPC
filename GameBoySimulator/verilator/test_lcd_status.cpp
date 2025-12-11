#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== LCD Status During Boot ===\n\n");

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

    printf("Monitoring boot ROM execution and LCD status...\n\n");

    bool boot_completed = false;
    bool lcd_turned_on = false;
    int lcd_on_cycle = -1;
    int boot_disable_cycle = -1;
    uint16_t last_pc = 0;

    for (int i = 0; i < 50000; i++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        bool boot_enabled = dut->dbg_boot_rom_enabled;
        bool lcd_on = dut->dbg_lcd_on;

        // Check LCD status
        if (lcd_on && !lcd_turned_on) {
            lcd_turned_on = true;
            lcd_on_cycle = i;
            printf("  [%6d] *** LCD TURNED ON *** (PC=$%04X)\n", i, pc);
        }

        // Check boot ROM disable
        if (!boot_enabled && !boot_completed) {
            boot_completed = true;
            boot_disable_cycle = i;
            printf("  [%6d] *** BOOT ROM DISABLED *** (PC=$%04X)\n", i, pc);
            
            // Run a bit more to see stable state
            for (int j = 0; j < 100; j++) {
                tick_with_sdram(dut, sdram);
            }
            break;
        }

        last_pc = pc;
    }

    printf("\n--- Final Status ---\n");
    printf("Boot ROM completed: %s", boot_completed ? "YES" : "NO");
    if (boot_disable_cycle >= 0) printf(" (cycle %d)", boot_disable_cycle);
    printf("\n");
    
    printf("LCD turned on: %s", lcd_turned_on ? "YES" : "NO");
    if (lcd_on_cycle >= 0) printf(" (cycle %d)", lcd_on_cycle);
    printf("\n");
    
    printf("Current LCD state: %s\n", dut->dbg_lcd_on ? "ON" : "OFF");
    printf("LCD mode: %d\n", dut->dbg_lcd_mode);
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);
    printf("Boot ROM enabled: %s\n", dut->dbg_boot_rom_enabled ? "YES" : "NO");

    if (boot_completed && lcd_turned_on) {
        printf("\n✓ SUCCESS: Boot ROM completed with LCD initialization!\n");
    } else if (boot_completed && !lcd_turned_on) {
        printf("\n⚠ Boot ROM completed but LCD did not turn on\n");
    } else {
        printf("\n✗ Boot ROM did not complete\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
