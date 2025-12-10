// Direct boot ROM memory access test
#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "Vtop__Syms.h"
#include "gb_test_common.h"
#include <cstdio>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

    printf("=== Boot ROM Memory Direct Access Test ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    printf("Step 1: Write test pattern to boot ROM\n");
    uint8_t test_pattern[] = {0x31, 0xFE, 0xFF, 0xC3, 0x10, 0x00, 0x18, 0xFE};

    dut->boot_download = 1;

    for (int addr = 0; addr < 8; addr += 2) {
        uint16_t word = test_pattern[addr];
        if (addr + 1 < 8) {
            word |= (test_pattern[addr + 1] << 8);
        }

        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;

        printf("  Writing addr=%d (0x%02X), data=0x%04X (bytes: 0x%02X 0x%02X)\n",
               addr, addr, word, word & 0xFF, (word >> 8) & 0xFF);

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }

        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
    }

    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("\nStep 2: Directly inspect boot ROM dpram memory array\n");

    // Access the boot ROM dpram memory through Verilator symbols table
    // Path: VerilatedSyms::TOP__top__gameboy__boot_rom
    auto* boot_rom = &dut->vlSymsp->TOP__top__gameboy__boot_rom;

    printf("  Checking memory at addresses 0x900-0x907 (DMG boot ROM area):\n");
    for (int i = 0x900; i < 0x908; i++) {
        uint8_t value = boot_rom->mem[i];
        printf("    mem[0x%03X] = 0x%02X", i, value);
        if (i >= 0x900 && i < 0x908) {
            int expected_idx = i - 0x900;
            if (expected_idx < 8) {
                uint8_t expected = test_pattern[expected_idx];
                printf(" (expected 0x%02X) %s", expected,
                       (value == expected) ? "✓" : "✗ MISMATCH!");
            }
        }
        printf("\n");
    }

    printf("\nStep 3: Release reset and let CPU try to read\n");
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    printf("  boot_rom_enabled = %d\n", dut->dbg_boot_rom_enabled);
    printf("  sel_boot_rom = %d\n", dut->dbg_sel_boot_rom);
    printf("  cpu_addr = 0x%04X\n", dut->dbg_cpu_addr);

    printf("\nStep 4: Monitor what CPU actually reads\n");
    for (int i = 0; i < 2000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t data = dut->dbg_cpu_do;

        if (rd_n == 0 && addr <= 0x0007) {
            printf("  Cycle %4d: CPU read addr=0x%04X, data=0x%02X", i, addr, data);
            if (addr < 8) {
                printf(" (expected 0x%02X) %s", test_pattern[addr],
                       (data == test_pattern[addr]) ? "✓" : "✗ MISMATCH!");
            }
            printf("\n");
        }

        tick_with_sdram(dut, sdram);

        if (addr > 0x0010) break;
    }

    delete sdram;
    delete dut;
    return 0;
}
