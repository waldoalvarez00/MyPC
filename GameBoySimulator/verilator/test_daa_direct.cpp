// Direct DAA test - runs a custom boot ROM that tests specific DAA cases
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>

// Reference DAA
uint16_t ref_daa(uint8_t a, uint8_t f) {
    int n = (f >> 6) & 1;
    int h = (f >> 5) & 1;
    int c = (f >> 4) & 1;
    int result = a;
    int carry_out = c;

    if (n == 0) {
        if (h || (result & 0x0F) > 9) { result += 0x06; }
        if (c || result > 0x9F) { result += 0x60; carry_out = 1; }
    } else {
        if (h) { result -= 0x06; }
        if (c) { result -= 0x60; }
    }
    result &= 0xFF;
    int z = (result == 0) ? 1 : 0;
    uint8_t f_out = (z << 7) | (n << 6) | (0 << 5) | (carry_out << 4);
    return (f_out << 8) | result;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Direct DAA Test ===\n\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Minimal ROM - just needs header
    uint8_t rom[0x8000];
    memset(rom, 0, sizeof(rom));
    rom[0x104] = 0xCE; rom[0x105] = 0xED;  // Nintendo logo bytes

    sdram->loadBinary(0, rom, sizeof(rom));

    // Custom boot ROM that tests DAA
    // Test plan:
    // 1. Load A with test value
    // 2. Load F with test flags (via PUSH AF / POP AF trick)
    // 3. Execute DAA
    // 4. Store result to 0xFF01 (serial) for capture
    // 5. Store flags to 0xFF01
    // 6. Repeat for different test cases

    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;

    // Test case 1: A=0x9A, F=0x00 (N=0, H=0, C=0)
    // Expected: A=0x00, C=1 (add 0x66)
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF; // LD SP, 0xFFFE
    boot[i++] = 0x3E; boot[i++] = 0x9A;                   // LD A, 0x9A
    boot[i++] = 0xF5;                                      // PUSH AF (A=0x9A, F=0x00 initially)
    boot[i++] = 0x01; boot[i++] = 0x00; boot[i++] = 0x00; // LD BC, 0x0000 (dummy)
    boot[i++] = 0xC1;                                      // POP BC (B=0x9A, C=0x00)
    boot[i++] = 0x79;                                      // LD A, C (A=0x00 = flags)
    boot[i++] = 0xE6; boot[i++] = 0x00;                   // AND 0x00 (clear flags to N=0,H=0,C=0)
    boot[i++] = 0xF5;                                      // PUSH AF
    boot[i++] = 0xC5;                                      // PUSH BC (B=0x9A)
    boot[i++] = 0xD1;                                      // POP DE (D=0x9A)
    boot[i++] = 0xE1;                                      // POP HL (H=0x00, L=F with cleared bits)
    boot[i++] = 0x7C;                                      // LD A, H (get 0x00)
    // Actually let me simplify - just use a direct approach

    memset(boot, 0, 256);
    i = 0;

    // Simpler approach: just test DAA with various starting conditions
    // and output results to serial port

    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF; // LD SP, 0xFFFE

    // Test 1: A=0x9A with F=0x00 (after AND A which clears N,H,C, sets Z)
    // But AND A will set Z since A&A = A. We need to set flags first.

    // Better approach: Use specific flag-setting instructions
    // XOR A -> Z=1, N=0, H=0, C=0, A=0
    // Then LD A, 0x9A

    boot[i++] = 0xAF;                    // XOR A -> A=0, Z=1, N=0, H=0, C=0
    boot[i++] = 0x3E; boot[i++] = 0x9A;  // LD A, 0x9A (flags unchanged: Z=1, N=0, H=0, C=0)
    boot[i++] = 0x27;                    // DAA
    // Expected: A=0x00, Z=1, N=0, H=0, C=1 -> F=0x90

    // Output A to serial
    boot[i++] = 0xE0; boot[i++] = 0x01;  // LDH (0xFF01), A - store A to serial data

    // Output F to serial (need to get F first)
    boot[i++] = 0xF5;                    // PUSH AF
    boot[i++] = 0xC1;                    // POP BC (B=A, C=F)
    boot[i++] = 0x79;                    // LD A, C (A=F)
    boot[i++] = 0xE0; boot[i++] = 0x01;  // LDH (0xFF01), A - store F to serial data

    // Trigger serial transfer
    boot[i++] = 0x3E; boot[i++] = 0x81;  // LD A, 0x81
    boot[i++] = 0xE0; boot[i++] = 0x02;  // LDH (0xFF02), A - trigger transfer

    // Test 2: A=0x00 with N=1, C=1 (after subtraction with borrow)
    // SUB A, 0x01 when A=0x00 -> A=0xFF, N=1, H=1, C=1
    boot[i++] = 0xAF;                    // XOR A -> A=0, flags cleared
    boot[i++] = 0xD6; boot[i++] = 0x01;  // SUB 0x01 -> A=0xFF, N=1, H=1, C=1, Z=0
    boot[i++] = 0x3E; boot[i++] = 0x00;  // LD A, 0x00 (keep flags)
    boot[i++] = 0x27;                    // DAA
    // With N=1, H=1, C=1: A = 0x00 - 0x06 - 0x60 = 0x9A
    // Expected: A=0x9A, F = Z=0, N=1, H=0, C=1 -> 0x50

    boot[i++] = 0xE0; boot[i++] = 0x01;  // Output A
    boot[i++] = 0xF5;                    // PUSH AF
    boot[i++] = 0xC1;                    // POP BC
    boot[i++] = 0x79;                    // LD A, C
    boot[i++] = 0xE0; boot[i++] = 0x01;  // Output F

    // Infinite loop
    boot[i++] = 0x18; boot[i++] = 0xFE;  // JR -2 (infinite loop)

    // Initialize
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

    // Run and capture writes to 0xFF01
    int cycles = 0;
    int max_cycles = 500000;
    uint8_t prev_wr_n = 1;
    int result_count = 0;

    printf("Running boot ROM DAA test...\n\n");

    while (cycles < max_cycles) {
        tick_with_sdram(dut, sdram);
        cycles++;

        // Detect writes
        bool cpu_write = (prev_wr_n == 1 && dut->dbg_cpu_wr_n == 0 && dut->dbg_cpu_mreq_n == 0);
        if (cpu_write) {
            uint16_t addr = dut->dbg_cpu_addr;
            uint8_t data = dut->dbg_cpu_do;

            if (addr == 0xFF01) {
                printf("Result %d: 0x%02X (at cycle %d, PC=0x%04X)\n",
                       result_count, data, cycles, dut->dbg_cpu_pc);
                result_count++;

                if (result_count >= 4) {
                    break;  // Got all results
                }
            }
        }
        prev_wr_n = dut->dbg_cpu_wr_n;
    }

    printf("\n=== Expected vs Actual ===\n");
    printf("Test 1: A=0x9A, F initial with Z=1,N=0,H=0,C=0\n");
    printf("  DAA expected: A=0x00, F=0x90 (Z=1, C=1)\n");
    printf("Test 2: A=0x00, F with N=1,H=1,C=1 (after SUB 1 from 0)\n");
    printf("  DAA expected: A=0x9A, F=0x50 (Z=0, N=1, C=1)\n");

    delete sdram;
    delete dut;

    return 0;
}
