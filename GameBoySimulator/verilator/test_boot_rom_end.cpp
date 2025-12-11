#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== Boot ROM End Trace ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);

    printf("Boot ROM end bytes:\n");
    printf("  $00B0: %02X %02X %02X = LD DE, $00D8\n", boot_rom[0xB0], boot_rom[0xB1], boot_rom[0xB2]);
    printf("  $00B3: %02X %02X %02X = JP $00FE\n", boot_rom[0xB3], boot_rom[0xB4], boot_rom[0xB5]);
    printf("  $00FE: %02X %02X    = LD ($FF50), A (disable boot ROM)\n", boot_rom[0xFE], boot_rom[0xFF]);
    printf("\n");

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
    dut->ioctl_dout = 0x00C3;  // NOP, JP
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Running until PC >= $00B0, then showing ALL PC changes:\n\n");

    uint16_t last_pc = 0xFFFF;
    int pc_changes = 0;
    bool show_all = false;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (pc >= 0x00B0 && !show_all) {
            show_all = true;
            printf("  [%6d] Reached $00B0+ - showing all PC changes:\n", i);
        }

        if (pc != last_pc) {
            pc_changes++;

            if (show_all) {
                printf("  [%6d] PC=$%04X boot_enabled=%d",
                       i, pc, boot_enabled ? 1 : 0);

                if (pc == 0x00B3) printf(" (JP $00FE)");
                if (pc == 0x00FE) printf(" (LD ($FF50),A - SHOULD DISABLE BOOT ROM)");
                if (pc == 0x0100) printf(" *** CART ENTRY ***");

                printf("\n");
            }

            last_pc = pc;
        }

        // Stop after seeing cart execution
        if (show_all && pc >= 0x0105) {
            printf("\n  Stopping after cart entry\n");
            break;
        }

        // Stop if we hit 100 PC changes in show_all mode
        if (show_all && pc_changes > 280) break;
    }

    printf("\n--- Results ---\n");
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);
    printf("Boot ROM enabled: %s\n", dut->dbg_boot_rom_enabled ? "YES" : "NO");

    if (!dut->dbg_boot_rom_enabled) {
        printf("\n✓ Boot ROM disabled successfully\n");
    } else {
        printf("\n✗ Boot ROM still enabled (bug: should be disabled at cart entry)\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
