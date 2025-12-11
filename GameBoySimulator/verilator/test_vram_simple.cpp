#include <verilated.h>
#include "Vtop.h"
#include "../sim/mister_sdram_model.h"
#include <stdio.h>

void tick(Vtop* dut, MisterSDRAMModel* sdram) {
    dut->clk_sys = 0;
    dut->eval();
    sdram->tick(dut->sd_cs, dut->sd_ras, dut->sd_cas, dut->sd_we,
                dut->sd_ba, dut->sd_addr, dut->sd_data_out,
                dut->sd_dqm, dut->sd_data_in, dut->sd_compl);
    dut->clk_sys = 1;
    dut->eval();
}

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency
    
    printf("Testing VRAM writes after dpram clock fix...\n");
    
    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    for (int i = 0; i < 100; i++) tick(dut, sdram);
    dut->reset = 0;
    for (int i = 0; i < 100; i++) tick(dut, sdram);
    
    // Monitor VRAM writes
    int vram_writes = 0;
    uint16_t last_addr = 0xFFFF;
    
    for (int i = 0; i < 10000 && vram_writes < 10; i++) {
        tick(dut, sdram);
        
        // Check for VRAM writes ($8000-$9FFF)
        if (dut->dbg_cpu_wr_n == 0 && 
            dut->dbg_cpu_addr >= 0x8000 && 
            dut->dbg_cpu_addr < 0xA000 &&
            dut->dbg_cpu_addr != last_addr) {
            printf("  [%5d] VRAM Write: [$%04X] = $%02X\n", 
                   i, dut->dbg_cpu_addr, dut->dbg_cpu_do);
            vram_writes++;
            last_addr = dut->dbg_cpu_addr;
        }
    }
    
    printf("\nResult: %d VRAM writes detected\n", vram_writes);
    printf("%s\n", vram_writes > 0 ? "✓ VRAM writes working!" : "✗ No VRAM writes detected");
    
    delete sdram;
    delete dut;
    return vram_writes > 0 ? 0 : 1;
}
