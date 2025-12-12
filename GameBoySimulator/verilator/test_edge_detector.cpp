#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    // MisterSDRAMModel ctor takes size in MB (not bytes).
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency
    
    printf("=== Edge Detector Diagnostic ===\n\n");
    
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
    
    printf("Looking for first few VRAM writes and showing signal states:\n\n");
    
    int vram_writes = 0;
    
    for (int i = 0; i < 1000 && vram_writes < 30; i++) {
        tick_with_sdram(dut, sdram);

        // Monitor ACTUAL VRAM writes (using vram_wren signal, not just cpu_wr_n)
        if (dut->dbg_vram_wren &&
            dut->dbg_cpu_addr >= 0x8000 &&
            dut->dbg_cpu_addr < 0xA000) {

            vram_writes++;
            printf("  [%4d] VRAM write #%d: addr=$%04X wr_n=%d old_wr_n=%d edge=%d vram_wren=%d\n",
                   i, vram_writes, dut->dbg_cpu_addr, dut->dbg_cpu_wr_n,
                   dut->dbg_old_cpu_wr_n, dut->dbg_cpu_wr_n_edge, dut->dbg_vram_wren);
        }
    }
    
    printf("\nPattern: If wr_n toggles 1→0→1→0, edge detector should produce ONE pulse.\n");
    printf("         But we're seeing ~20 writes while wr_n stays low (wr_n=0 for 20 cycles).\n");
    printf("\nThis suggests cpu_wr_n stays low for the entire write operation,\n");
    printf("which is normal Z80 behavior, but our edge detector isn't working.\n");
    
    delete sdram;
    delete dut;
    return 0;
}
