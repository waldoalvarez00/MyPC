// Test LCD timing - check how many cycles per scanline
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== LCD Timing Analysis ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Minimal ROM 
    uint8_t rom[32768];
    memset(rom, 0, sizeof(rom));
    rom[0x100] = 0x00; // NOP
    rom[0x101] = 0x18; // JR -2 (infinite loop)
    rom[0x102] = 0xFE;
    
    // Nintendo logo (required)
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

    // Boot ROM that enables LCD
    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF; // LD SP, 0xFFFE
    boot[i++] = 0x3E; boot[i++] = 0x91;                   // LD A, 0x91
    boot[i++] = 0xE0; boot[i++] = 0x40;                   // LDH (0x40), A - enable LCD
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01; // JP 0x0100

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

    // Init cart
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 256);

    // Release reset
    dut->reset = 0;
    
    // Wait for PC to reach 0x0100
    int cycles = 0;
    while (dut->dbg_cpu_pc != 0x0100 && cycles < 10000) {
        run_cycles_with_sdram(dut, sdram, 1);
        cycles++;
    }
    printf("Reached PC=0x0100 at cycle %d\n", cycles);
    printf("LCDC=0x%02X, LY=%d at entry\n", dut->dbg_lcdc, dut->dbg_video_ly);

    // Now measure LY timing
    int prev_ly = dut->dbg_video_ly;
    int ly_change_cycles[20];
    int ly_changes = 0;
    int start_cycle = cycles;
    
    // Run and track LY changes
    for (int j = 0; j < 200000 && ly_changes < 20; j++) {
        run_cycles_with_sdram(dut, sdram, 1);
        cycles++;
        
        int ly = dut->dbg_video_ly;
        if (ly != prev_ly) {
            ly_change_cycles[ly_changes] = cycles - start_cycle;
            printf("LY %d -> %d at cycle %d (delta from start: %d)\n", 
                   prev_ly, ly, cycles, cycles - start_cycle);
            if (ly_changes > 0) {
                printf("  Cycles since last LY change: %d\n", 
                       ly_change_cycles[ly_changes] - ly_change_cycles[ly_changes-1]);
            }
            prev_ly = ly;
            ly_changes++;
            start_cycle = cycles;
        }
    }
    
    printf("\nExpected: 456 cycles per scanline (114 M-cycles * 4)\n");
    
    delete sdram;
    delete dut;
    return 0;
}
