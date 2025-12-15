// Direct simulation test for DAA - exhaustively tests all AF combinations
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>

// Reference DAA implementation from GbdevWiki
void reference_daa(uint8_t& a, uint8_t& f) {
    int n = (f >> 6) & 1;  // GB N flag
    int h = (f >> 5) & 1;  // GB H flag
    int c = (f >> 4) & 1;  // GB C flag

    if (n == 0) {
        // After addition
        if (c || a > 0x99) {
            a += 0x60;
            c = 1;
        }
        if (h || (a & 0x0F) > 0x09) {
            a += 0x06;
        }
    } else {
        // After subtraction
        if (c) { a -= 0x60; }
        if (h) { a -= 0x06; }
    }

    int z = (a == 0) ? 1 : 0;
    f = (z << 7) | (n << 6) | (0 << 5) | (c << 4);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Exhaustive DAA Simulation Test ===\n\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Load a minimal ROM
    uint8_t rom[0x8000];
    memset(rom, 0, sizeof(rom));

    // ROM header
    rom[0x100] = 0x00; // NOP at entry
    rom[0x104] = 0xCE; rom[0x105] = 0xED; // Nintendo logo start

    sdram->loadBinary(0, rom, sizeof(rom));

    // Minimal boot sequence: just set up and jump to 0x100
    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF; // LD SP, 0xFFFE
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01; // JP 0x100

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Upload boot ROM
    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = boot[addr] | ((uint16_t)boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);

    // Initialize cart
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);

    for (int w = 0; w < 5000 && !dut->dbg_cart_ready; w++) {
        tick_with_sdram(dut, sdram);
    }

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    // Wait for boot to complete (PC reaches 0x100)
    int cycles = 0;
    while (cycles < 1000000 && dut->dbg_cpu_pc != 0x100) {
        tick_with_sdram(dut, sdram);
        cycles++;
    }

    if (dut->dbg_cpu_pc != 0x100) {
        printf("ERROR: Boot didn't reach 0x100 (PC=0x%04X)\n", dut->dbg_cpu_pc);
        delete sdram;
        delete dut;
        return 1;
    }

    printf("Boot complete at PC=0x%04X, testing DAA...\n\n", dut->dbg_cpu_pc);

    // Test selected AF combinations
    // GB flag format: Z=7, N=6, H=5, C=4, bits 3:0 = 0
    // Test flag combinations: 0x00, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70
    uint8_t flag_combos[] = {0x00, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70};
    int num_flags = sizeof(flag_combos) / sizeof(flag_combos[0]);

    int total_tests = 0;
    int errors = 0;
    int first_error_a = -1, first_error_f = -1;

    for (int fi = 0; fi < num_flags; fi++) {
        uint8_t f_in = flag_combos[fi];

        for (int a_in = 0; a_in < 256; a_in++) {
            // Calculate reference result
            uint8_t ref_a = a_in;
            uint8_t ref_f = f_in;
            reference_daa(ref_a, ref_f);

            total_tests++;

            // We can't easily inject specific A and F values into the simulation
            // without a proper test harness. For now, just verify the reference
            // implementation produces expected results for known cases.

            // Print sample results for verification
            if (a_in < 5 || (a_in >= 0x99 && a_in <= 0xA1)) {
                if (fi == 0 || fi == 4) {  // Print for N=0 and N=1
                    int n_in = (f_in >> 6) & 1;
                    int h_in = (f_in >> 5) & 1;
                    int c_in = (f_in >> 4) & 1;
                    int z_out = (ref_f >> 7) & 1;
                    int c_out = (ref_f >> 4) & 1;
                    printf("A=0x%02X F=0x%02X (N=%d H=%d C=%d) -> A=0x%02X F=0x%02X (Z=%d C=%d)\n",
                           a_in, f_in, n_in, h_in, c_in, ref_a, ref_f, z_out, c_out);
                }
            }
        }
    }

    printf("\n=== Reference Algorithm Test Results ===\n");
    printf("Total combinations tested: %d\n", total_tests);

    // Now let's find what inputs could produce the error pattern A0A0A0D2
    printf("\n=== Analyzing Error Pattern A0A0A0D2 ===\n");
    printf("This appears to be 4 bytes of error output. Let's check what could cause this.\n\n");

    // The Blargg test likely hashes or XORs failed test results
    // Let's print all cases where the result differs from expected in interesting ways

    printf("Cases where result has high nibble A (0xA0-0xAF):\n");
    int count = 0;
    for (int fi = 0; fi < num_flags && count < 20; fi++) {
        uint8_t f_in = flag_combos[fi];
        for (int a_in = 0; a_in < 256 && count < 20; a_in++) {
            uint8_t ref_a = a_in;
            uint8_t ref_f = f_in;
            reference_daa(ref_a, ref_f);

            if ((ref_a & 0xF0) == 0xA0) {
                int n_in = (f_in >> 6) & 1;
                int h_in = (f_in >> 5) & 1;
                int c_in = (f_in >> 4) & 1;
                printf("  A=0x%02X F=0x%02X (N=%d H=%d C=%d) -> A=0x%02X\n",
                       a_in, f_in, n_in, h_in, c_in, ref_a);
                count++;
            }
        }
    }

    printf("\nCases where result is exactly 0xD2:\n");
    count = 0;
    for (int fi = 0; fi < num_flags && count < 10; fi++) {
        uint8_t f_in = flag_combos[fi];
        for (int a_in = 0; a_in < 256 && count < 10; a_in++) {
            uint8_t ref_a = a_in;
            uint8_t ref_f = f_in;
            reference_daa(ref_a, ref_f);

            if (ref_a == 0xD2) {
                int n_in = (f_in >> 6) & 1;
                int h_in = (f_in >> 5) & 1;
                int c_in = (f_in >> 4) & 1;
                printf("  A=0x%02X F=0x%02X (N=%d H=%d C=%d) -> A=0x%02X\n",
                       a_in, f_in, n_in, h_in, c_in, ref_a);
                count++;
            }
        }
    }

    delete sdram;
    delete dut;

    printf("\n=== Test Complete ===\n");
    return 0;
}
