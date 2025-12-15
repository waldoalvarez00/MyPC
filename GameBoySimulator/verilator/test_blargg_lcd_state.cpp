// Test to check LCD state during actual Blargg test
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== LCD State During Blargg Test ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Load actual ROM
    FILE* rom_file = fopen("cpu_instrs/individual/01-special.gb", "rb");
    if (!rom_file) {
        printf("ERROR: Cannot open ROM\n");
        return 1;
    }
    fseek(rom_file, 0, SEEK_END);
    size_t rom_size = ftell(rom_file);
    fseek(rom_file, 0, SEEK_SET);
    uint8_t* rom = new uint8_t[rom_size];
    fread(rom, 1, rom_size, rom_file);
    fclose(rom_file);
    
    // Initialize with post-boot state
    init_post_boot(dut, sdram, rom, rom_size);
    
    printf("ROM loaded, starting simulation\n\n");

    // Monitor LCD state during execution
    int total_cycles = 0;
    int prev_ly = -1;
    int ly_changes = 0;
    
    for (int i = 0; i < 500000; i++) {
        run_cycles_with_sdram(dut, sdram, 1);
        total_cycles++;
        
        int ly = dut->dbg_video_ly;
        if (ly != prev_ly) {
            ly_changes++;
            if (ly_changes <= 10 || ly == 0 || ly == 144) {
                printf("Cycle %d: LY changed to %d\n", total_cycles, ly);
            }
            prev_ly = ly;
        }
        
        if (i % 50000 == 0) {
            printf("\n=== Cycle %d ===\n", total_cycles);
            printf("  LCDC: 0x%02X (LCD ON: %d)\n", dut->dbg_lcdc, (dut->dbg_lcdc >> 7) & 1);
            printf("  lcd_on: %d\n", dut->dbg_lcd_on);
            printf("  lcd_clkena: %d\n", dut->dbg_lcd_clkena);
            printf("  lcd_mode: %d\n", dut->dbg_lcd_mode);
            printf("  video_ly: %d\n", dut->dbg_video_ly);
            printf("  ce_cpu: %d\n", dut->dbg_ce_cpu);
            printf("  cpu_pc: 0x%04X\n", dut->dbg_cpu_pc);
            printf("  LY changes so far: %d\n", ly_changes);
            printf("\n");
        }
    }
    
    printf("\nTotal LY changes: %d\n", ly_changes);
    printf("Final LY: %d\n", dut->dbg_video_ly);
    
    delete[] rom;
    delete sdram;
    delete dut;
    return 0;
}
