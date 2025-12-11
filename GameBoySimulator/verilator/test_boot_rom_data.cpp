#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== Verification 1: Boot ROM Binary Loaded ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("ERROR: Cannot find dmg_boot.bin\n");
        return 1;
    }
    fread(boot_rom, 1, 256, f);
    fclose(f);

    printf("Boot ROM file contents at critical addresses:\n");
    printf("  $0000-$0003: %02X %02X %02X %02X\n",
           boot_rom[0], boot_rom[1], boot_rom[2], boot_rom[3]);
    printf("  $0004-$0007: %02X %02X %02X %02X (LD HL, nn instruction)\n",
           boot_rom[4], boot_rom[5], boot_rom[6], boot_rom[7]);
    printf("  $0008-$000B: %02X %02X %02X %02X\n",
           boot_rom[8], boot_rom[9], boot_rom[10], boot_rom[11]);
    printf("\n");

    if (boot_rom[4] == 0x21) {
        uint16_t hl_value = boot_rom[5] | (boot_rom[6] << 8);
        printf("✓ Opcode at $0004 is $21 (LD HL, nn)\n");
        printf("✓ HL should be loaded with: $%04X\n", hl_value);

        if (hl_value == 0x0104) {
            printf("✓ HL value is $0104 (Nintendo logo address) - CORRECT!\n");
        } else {
            printf("✗ HL value is $%04X (expected $0104) - WRONG!\n", hl_value);
        }
    } else {
        printf("✗ Opcode at $0004 is $%02X (expected $21 for LD HL, nn)\n", boot_rom[4]);
    }
    printf("\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM into hardware
    printf("Loading boot ROM into hardware...\n");
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
    printf("✓ Boot ROM loaded (%d bytes in %d 16-bit writes)\n\n", 256, 128);

    // Verify by reading back
    printf("Reading back boot ROM data from CPU bus...\n");
    printf("(CPU will read from boot ROM addresses $0004-$0006)\n\n");

    // Simulate cart with minimal header
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

    // Monitor CPU reads from boot ROM area
    printf("Monitoring CPU reads from $0004-$0006:\n");

    uint8_t read_values[3] = {0xFF, 0xFF, 0xFF};
    bool found_reads[3] = {false, false, false};

    for (int i = 0; i < 500; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t data_in = dut->dbg_cpu_di;
        uint16_t pc = dut->dbg_cpu_pc;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect reads from critical addresses
        if (rd_n == 0 && addr >= 0x0004 && addr <= 0x0006 && boot_enabled) {
            int idx = addr - 0x0004;
            if (!found_reads[idx]) {
                read_values[idx] = data_in;
                found_reads[idx] = true;
                printf("  [%6d] PC=$%04X reading addr=$%04X: data=$%02X (boot_rom_enabled=%d)\n",
                       i, pc, addr, data_in, boot_enabled);
            }
        }

        tick_with_sdram(dut, sdram);

        // Stop after instruction fetch completes
        if (found_reads[0] && found_reads[1] && found_reads[2]) {
            break;
        }
    }

    printf("\n--- Verification Results ---\n");
    printf("Expected from file:\n");
    printf("  $0004: $%02X (opcode)\n", boot_rom[4]);
    printf("  $0005: $%02X (HL low byte)\n", boot_rom[5]);
    printf("  $0006: $%02X (HL high byte)\n", boot_rom[6]);
    printf("\nActual read by CPU:\n");
    printf("  $0004: $%02X %s\n", read_values[0],
           found_reads[0] ? (read_values[0] == boot_rom[4] ? "✓" : "✗") : "NOT READ");
    printf("  $0005: $%02X %s\n", read_values[1],
           found_reads[1] ? (read_values[1] == boot_rom[5] ? "✓" : "✗") : "NOT READ");
    printf("  $0006: $%02X %s\n", read_values[2],
           found_reads[2] ? (read_values[2] == boot_rom[6] ? "✓" : "✗") : "NOT READ");

    bool all_correct = found_reads[0] && found_reads[1] && found_reads[2] &&
                       read_values[0] == boot_rom[4] &&
                       read_values[1] == boot_rom[5] &&
                       read_values[2] == boot_rom[6];

    if (all_correct) {
        printf("\n✅ PASS: Boot ROM data matches file!\n");
    } else {
        printf("\n❌ FAIL: Boot ROM data mismatch or not read!\n");
        if (!found_reads[0] || !found_reads[1] || !found_reads[2]) {
            printf("   Possible cause: CPU not reading from boot ROM addresses\n");
        } else {
            printf("   Possible cause: Boot ROM not loaded correctly or address decode issue\n");
        }
    }

    delete sdram;
    delete dut;
    return all_correct ? 0 : 1;
}
