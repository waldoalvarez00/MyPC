// Test boot ROM loading with different sizes
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>

void load_test_program(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* program, int size) {
    dut->boot_download = 1;

    for (int addr = 0; addr < size; addr += 2) {
        uint16_t word = program[addr];
        if (addr + 1 < size) {
            word |= (program[addr + 1] << 8);
        }

        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }

        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
    }

    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);
}

void test_size(int size) {
    printf("\n=== Testing boot ROM size: %d bytes ===\n", size);

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    // Create test program
    uint8_t* program = new uint8_t[size];
    memset(program, 0, size);

    // Put a recognizable pattern at the start
    if (size >= 8) {
        program[0] = 0x31;  // LD SP, $FFFE
        program[1] = 0xFE;
        program[2] = 0xFF;
        program[3] = 0xC3;  // JP $0010
        program[4] = 0x10;
        program[5] = 0x00;
        program[6] = 0x18;  // JR
        program[7] = 0xFE;
    }

    // Initialize with reset ACTIVE
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM while reset is active
    load_test_program(dut, sdram, program, size);

    // Simulate cart download while reset is active
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Release reset
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Monitor what CPU reads
    printf("CPU reads:\n");
    int read_count = 0;
    for (int i = 0; i < 2000 && read_count < 10; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t data = dut->dbg_cpu_do;

        if (rd_n == 0 && addr < 8) {
            printf("  addr=0x%04X, data=0x%02X (expected 0x%02X) %s\n",
                   addr, data, program[addr],
                   (data == program[addr]) ? "✓" : "✗ FAIL");
            read_count++;
        }

        tick_with_sdram(dut, sdram);

        if (addr > 0x0020) break;
    }

    delete[] program;
    delete sdram;
    delete dut;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    // Test different sizes
    test_size(8);      // Very small
    test_size(16);     // Small
    test_size(18);     // What the failing test uses
    test_size(32);     // Medium
    test_size(64);     // Larger
    test_size(128);    // Even larger
    test_size(256);    // Full boot ROM

    return 0;
}
