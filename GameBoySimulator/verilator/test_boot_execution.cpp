#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency
    
    printf("=== Boot ROM Execution Trace ===\n\n");
    
    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("ERROR: Could not load dmg_boot.bin\n");
        return 1;
    }
    fread(boot_rom, 1, 256, f);
    fclose(f);
    
    // Show first few bytes of boot ROM
    printf("Boot ROM first 32 bytes:\n");
    for (int i = 0; i < 32; i++) {
        printf("%02X ", boot_rom[i]);
        if ((i % 16) == 15) printf("\n");
    }
    printf("\n");
    
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
    
    // Simulate cart header
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    
    run_cycles_with_sdram(dut, sdram, 100);
    
    // Release reset
    dut->reset = 0;
    
    printf("\n--- PC Trace (showing execution path) ---\n");
    
    uint16_t last_pc = 0;
    int pc_changes = 0;
    bool reached_end = false;
    
    for (int i = 0; i < 100000 && pc_changes < 200; i++) {
        tick_with_sdram(dut, sdram);
        
        uint16_t pc = dut->dbg_cpu_pc;
        
        if (pc != last_pc && dut->dbg_boot_rom_enabled) {
            pc_changes++;
            printf("  [%6d] PC=$%04X", i, pc);
            
            // Mark key addresses
            if (pc == 0x0000) printf(" (start)");
            if (pc == 0x0005) printf(" (logo copy start)");
            if (pc == 0x000C) printf(" (logo copy loop)");
            if (pc >= 0x001E && pc <= 0x0027) printf(" (logo check)");
            if (pc >= 0x0028 && pc <= 0x0034) printf(" (audio init)");
            if (pc >= 0x0035 && pc <= 0x00FC) printf(" (video init area)");
            if (pc == 0x00FC) printf(" (disable boot ROM)");
            if (pc == 0x0100) {
                printf(" (CART START - boot complete!)");
                reached_end = true;
            }
            
            printf("\n");
            
            last_pc = pc;
        }
        
        // Check if boot ROM disabled
        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  [%6d] Boot ROM DISABLED - jumped to cart\n", i);
            break;
        }
    }
    
    printf("\n--- Results ---\n");
    printf("PC changes: %d\n", pc_changes);
    printf("Reached cart entry: %s\n", reached_end ? "YES" : "NO");
    printf("Boot ROM still enabled: %s\n", dut->dbg_boot_rom_enabled ? "YES" : "NO");
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);
    
    printf("\n--- Analysis ---\n");
    if (pc_changes < 20) {
        printf("✗ Very few PC changes - CPU may be stuck\n");
    } else if (!reached_end) {
        printf("⚠ Boot ROM executing but didn't reach cart entry\n");
        printf("  Last PC: $%04X\n", last_pc);
    } else {
        printf("✓ Boot ROM executed to completion\n");
    }
    
    delete sdram;
    delete dut;
    return 0;
}
