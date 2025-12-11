#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency
    
    printf("=== Debug JP Instruction Reads ===\n\n");
    
    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    
    // JP instruction test: JP $0010 at address $0003
    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0xC3, 0x10, 0x00,  // JP $0010
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x18, 0xFE         // JR $10 (loop)
    };
    
    // Load boot ROM
    load_test_program(dut, sdram, program, sizeof(program));
    
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
    
    // Monitor what CPU reads
    printf("CPU reads from boot ROM:\n");
    uint16_t last_addr = 0xFFFF;
    int read_count = 0;
    
    for (int i = 0; i < 2000 && read_count < 30; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t data = dut->dbg_cpu_do;
        
        if (rd_n == 0 && addr != last_addr && addr < 0x0020) {
            uint8_t expected = (addr < sizeof(program)) ? program[addr] : 0x00;
            printf("  [%4d] addr=$%04X data=0x%02X expected=0x%02X %s\n",
                   i, addr, data, expected,
                   (data == expected) ? "✓" : "✗ MISMATCH!");
            last_addr = addr;
            read_count++;
        }
        
        tick_with_sdram(dut, sdram);
        
        if (addr > 0x00D0) break;
    }
    
    delete sdram;
    delete dut;
    return 0;
}
