// Check CPU clock enable ratio
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== CPU Clock Enable Ratio Test ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Minimal ROM
    uint8_t rom[32768];
    memset(rom, 0, sizeof(rom));
    rom[0x100] = 0x00; rom[0x101] = 0x18; rom[0x102] = 0xFE;
    const uint8_t logo[48] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E,
    };
    memcpy(&rom[0x104], logo, 48);
    sdram->loadBinary(0, rom, sizeof(rom));

    // Boot ROM
    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;
    boot[i++] = 0x3E; boot[i++] = 0x91;
    boot[i++] = 0xE0; boot[i++] = 0x40;
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

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

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 256);

    dut->reset = 0;
    
    // Count ce_cpu pulses between LY changes
    int cycles = 0;
    int ce_cpu_count = 0;
    int prev_ly = -1;
    
    // Wait for LCD to start
    while (dut->dbg_lcdc != 0x91 && cycles < 10000) {
        run_cycles_with_sdram(dut, sdram, 1);
        cycles++;
    }
    printf("LCD enabled at cycle %d\n", cycles);
    
    prev_ly = dut->dbg_video_ly;
    int start_ce_count = 0;
    int ly_count = 0;
    
    for (int j = 0; j < 100000 && ly_count < 5; j++) {
        // Check ce_cpu before clock
        int ce_before = dut->dbg_ce_cpu;
        
        run_cycles_with_sdram(dut, sdram, 1);
        cycles++;
        
        // Count ce_cpu rising edges
        if (dut->dbg_ce_cpu && !ce_before) {
            ce_cpu_count++;
        }
        
        int ly = dut->dbg_video_ly;
        if (ly != prev_ly) {
            printf("LY %d -> %d: %d ce_cpu pulses (system cycles: %d)\n", 
                   prev_ly, ly, ce_cpu_count - start_ce_count, j);
            start_ce_count = ce_cpu_count;
            prev_ly = ly;
            ly_count++;
        }
    }
    
    printf("\nTotal ce_cpu pulses: %d in %d system cycles\n", ce_cpu_count, cycles);
    printf("Ratio: %.2f system cycles per ce_cpu\n", (float)cycles / ce_cpu_count);
    printf("\nExpected: 456 ce_cpu per scanline (114 M-cycles * 4 T-cycles)\n");
    
    delete sdram;
    delete dut;
    return 0;
}
