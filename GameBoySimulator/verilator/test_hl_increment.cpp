#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency
    
    printf("=== HL Register Increment Test ===\n\n");
    
    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);
    
    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM
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
    
    // Simulate cart
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
    
    printf("Monitoring LD (HL+), A instruction execution:\n");
    printf("Boot ROM $0006 = $22 (LD (HL+), A)\n\n");
    
    uint16_t last_pc = 0;
    int vram_writes = 0;
    uint16_t last_vram_addr = 0;
    
    for (int i = 0; i < 20000; i++) {
        tick_with_sdram(dut, sdram);
        
        uint16_t pc = dut->dbg_cpu_pc;
        
        // When PC reaches $0006 (LD (HL+), A instruction)
        if (pc == 0x0006 && last_pc != 0x0006 && vram_writes < 10) {
            printf("  [%6d] At LD (HL+),A instruction\n", i);
        }
        
        // Monitor VRAM writes
        if (dut->dbg_cpu_wr_n == 0 && 
            dut->dbg_cpu_addr >= 0x8000 && 
            dut->dbg_cpu_addr < 0xA000) {
            
            vram_writes++;
            
            if (vram_writes <= 20 || (vram_writes % 100) == 0) {
                printf("  [%6d] VRAM[%04X] = $%02X (write #%d)\n",
                       i, dut->dbg_cpu_addr, dut->dbg_cpu_do, vram_writes);
                
                if (dut->dbg_cpu_addr == last_vram_addr && vram_writes > 1) {
                    printf("           ^^^ SAME ADDRESS - HL not incrementing!\n");
                }
                
                last_vram_addr = dut->dbg_cpu_addr;
            }
        }
        
        last_pc = pc;
        
        if (vram_writes > 500) {
            printf("\n... (stopped after 500 VRAM writes)\n");
            break;
        }
    }
    
    printf("\n--- Results ---\n");
    printf("VRAM writes: %d\n", vram_writes);
    printf("Last VRAM address: $%04X\n", last_vram_addr);
    
    if (last_vram_addr == 0x8000 && vram_writes > 10) {
        printf("\n✗ BUG CONFIRMED: HL register not incrementing!\n");
        printf("  LD (HL+), A writes to same address repeatedly\n");
        printf("  This is a Z80 CPU core bug in GameBoy mode\n");
    }
    
    delete sdram;
    delete dut;
    return 0;
}
