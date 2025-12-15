// Run Blargg test until completion, check serial output
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>
#include <string>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Blargg Test Runner ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Load ROM
    const char* rom_path = argc > 1 ? argv[1] : "cpu_instrs/individual/01-special.gb";
    FILE* f = fopen(rom_path, "rb");
    if (!f) { printf("Cannot open %s\n", rom_path); return 1; }
    fseek(f, 0, SEEK_END);
    size_t rom_size = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t* rom = new uint8_t[rom_size];
    fread(rom, 1, rom_size, f);
    fclose(f);
    printf("Loaded ROM: %zu bytes\n", rom_size);

    sdram->loadBinary(0, rom, rom_size);

    // Boot ROM with LCD enable
    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;
    boot[i++] = 0x3E; boot[i++] = 0x91;
    boot[i++] = 0xE0; boot[i++] = 0x40;
    boot[i++] = 0x06; boot[i++] = 0x00;
    boot[i++] = 0x0E; boot[i++] = 0x13;
    boot[i++] = 0x16; boot[i++] = 0x00;
    boot[i++] = 0x1E; boot[i++] = 0xD8;
    boot[i++] = 0x26; boot[i++] = 0x01;
    boot[i++] = 0x2E; boot[i++] = 0x4D;
    boot[i++] = 0xD5;
    boot[i++] = 0x16; boot[i++] = 0x01;
    boot[i++] = 0x1E; boot[i++] = 0xB0;
    boot[i++] = 0xD5;
    boot[i++] = 0xF1;
    boot[i++] = 0xD1;
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
    
    // Capture serial output (SB register at 0xFF01)
    std::string serial_output;
    uint8_t last_sb = 0;
    int cycles = 0;
    int max_cycles = 50000000;  // 50M cycles
    
    printf("Running test...\n");
    
    while (cycles < max_cycles) {
        run_cycles_with_sdram(dut, sdram, 1000);
        cycles += 1000;
        
        // Check serial control register (SC at 0xFF02) for transfer complete
        // When bit 7 goes high, a byte was sent to SB (0xFF01)
        // For Blargg tests, output goes to serial
        
        if (cycles % 1000000 == 0) {
            printf("  %dM cycles, PC=0x%04X, LY=%d\n", cycles/1000000, dut->dbg_cpu_pc, dut->dbg_video_ly);
        }
        
        // Check for HALT at specific addresses that indicate pass/fail
        // Blargg tests typically HALT at end with result code in A
        if (dut->dbg_cpu_pc == 0xC003 || dut->dbg_cpu_pc == 0xC004 || dut->dbg_cpu_pc == 0xC005) {
            // Test is in its main loop - check A register for result
            static int loop_count = 0;
            loop_count++;
            if (loop_count > 100000) {
                printf("\nTest appears to be in infinite loop at PC=0x%04X\n", dut->dbg_cpu_pc);
                printf("A=%02X (result code)\n", dut->dbg_cpu_acc);
                break;
            }
        }
    }
    
    printf("\nFinal state: PC=0x%04X, A=0x%02X\n", dut->dbg_cpu_pc, dut->dbg_cpu_acc);
    
    delete[] rom;
    delete sdram;
    delete dut;
    return 0;
}
