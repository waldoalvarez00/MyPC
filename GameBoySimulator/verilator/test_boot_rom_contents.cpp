// Test to verify boot ROM contents after loading
#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <cstdio>

void load_and_verify(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* program, int size) {
    printf("Loading %d bytes...\n", size);

    dut->boot_download = 1;
    for (int addr = 0; addr < size; addr += 2) {
        uint16_t word = program[addr];
        if (addr + 1 < size) word |= (program[addr + 1] << 8);

        printf("  Write addr=%d (0x%02X), data=0x%04X (bytes: 0x%02X 0x%02X)\n",
               addr, addr, word, word & 0xFF, (word >> 8) & 0xFF);

        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    printf("\nVerifying by reading back through CPU...\n");

    // Now try to read back by letting CPU execute
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    printf("First 10 bytes CPU will see:\n");
    uint16_t last_addr = 0xFFFF;
    int count = 0;

    for (int i = 0; i < 1000 && count < 20; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cpu_addr != last_addr) {
            printf("  Cycle %5d: addr=$%04X\n", i, dut->dbg_cpu_addr);
            last_addr = dut->dbg_cpu_addr;
            count++;
        }
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Boot ROM Loading Test ===\n\n");

    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0xC3, 0x10, 0x00,  // JP $0010
        0x00, 0x00         // Padding
    };

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    load_and_verify(dut, sdram, program, sizeof(program));

    delete sdram;
    delete dut;
    return 0;
}
