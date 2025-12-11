#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
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

    printf("=== Debug JP Instruction Execution ===\n\n");
    
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // $00: LD SP, $FFFE
        0xC3, 0x10, 0x00,  // $03: JP $0010  
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // Padding
        0x18, 0xFE         // $10: JR $10 (loop)
    };

    load_test_program(dut, sdram, program, sizeof(program));

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    printf("CPU reads from boot ROM:\n");
    for (int i = 0; i < 2000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t data = dut->dbg_cpu_do;

        if (rd_n == 0 && addr < 0x0020) {
            uint8_t expected = (addr < sizeof(program)) ? program[addr] : 0x00;
            printf("  [%4d] addr=$%04X data=0x%02X expected=0x%02X %s\n",
                   i, addr, data, expected, (data == expected) ? "✓" : "✗");
        }

        tick_with_sdram(dut, sdram);
        if (addr > 0x00D0) break;
    }

    delete sdram;
    delete dut;
    return 0;
}
