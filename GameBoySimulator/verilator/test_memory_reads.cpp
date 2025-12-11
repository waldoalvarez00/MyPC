// Test to monitor what the CPU actually reads from memory
#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <cstdio>

void load_program(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* program, int size) {
    dut->boot_download = 1;
    for (int addr = 0; addr < size; addr += 2) {
        uint16_t word = program[addr];
        if (addr + 1 < size) word |= (program[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Memory Read Monitor Test ===\n");
    printf("Program: JP $0010\n");
    printf("  $0000: 31 FE FF  (LD SP, $FFFE)\n");
    printf("  $0003: C3 10 00  (JP $0010)\n\n");

    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0xC3, 0x10, 0x00,  // JP $0010
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // Padding
        0x18, 0xFE         // JR $10 (loop)
    };

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    load_program(dut, sdram, program, sizeof(program));

    // Simulate cart download
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

    printf("Monitoring reads (showing when rd_n=0, i.e., reading):\n");
    printf("Cycle | Addr  | rd_n | Data | Notes\n");
    printf("------|-------|------|------|------\n");

    for (int i = 0; i < 5000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t data = dut->dbg_cpu_do;  // Data being read by CPU

        // Log reads
        if (rd_n == 0 && dut->dbg_boot_rom_enabled) {
            printf("%5d | $%04X |  %d   | $%02X  | ", i, addr, rd_n, data);

            if (addr == 0x0000) printf("LD SP opcode");
            else if (addr == 0x0001) printf("SP low byte");
            else if (addr == 0x0002) printf("SP high byte");
            else if (addr == 0x0003) printf("JP opcode (should be C3)");
            else if (addr == 0x0004) printf("JP target low (should be 10)");
            else if (addr == 0x0005) printf("JP target high (should be 00)");

            printf("\n");

            if (addr > 0x0010) break;  // Stop after JP target area
        }

        tick_with_sdram(dut, sdram);
    }

    delete sdram;
    delete dut;
    return 0;
}
