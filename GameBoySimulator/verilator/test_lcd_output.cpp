#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    
    printf("=== LCD/VGA Output Diagnostic ===\n\n");
    
    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) {
        f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    }
    if (!f) {
        printf("ERROR: Could not load dmg_boot.bin\n");
        return 1;
    }
    fread(boot_rom, 1, 256, f);
    fclose(f);
    printf("✓ Loaded DMG boot ROM (256 bytes)\n");
    
    // Initialize with reset
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM via boot_download interface
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
    
    // Simulate minimal cart header
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;  // JP $0150
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    
    run_cycles_with_sdram(dut, sdram, 100);
    
    // Release reset
    dut->reset = 0;
    
    printf("\n--- Monitoring LCD/VGA Output ---\n");
    
    int vram_writes = 0;
    int lcd_pixels_output = 0;
    int nonzero_pixels = 0;
    bool lcd_turned_on = false;
    int vsync_count = 0;
    bool last_vsync = false;
    int cycles_until_first_pixel = -1;
    int cycles_until_lcd_on = -1;
    
    uint8_t first_nonzero_pixel = 0;
    int first_pixel_cycle = 0;
    
    for (int i = 0; i < 500000; i++) {
        tick_with_sdram(dut, sdram);
        
        // Monitor VRAM writes
        if (dut->dbg_cpu_wr_n == 0 && 
            dut->dbg_cpu_addr >= 0x8000 && 
            dut->dbg_cpu_addr < 0xA000) {
            vram_writes++;
            
            if (vram_writes <= 5) {
                printf("  [%6d] VRAM Write: [$%04X] = $%02X\n", 
                       i, dut->dbg_cpu_addr, dut->dbg_cpu_do);
            } else if (vram_writes == 6) {
                printf("  ... (more VRAM writes)\n");
            }
        }
        
        // Check if LCD is on
        if (dut->dbg_lcd_on && !lcd_turned_on) {
            lcd_turned_on = true;
            cycles_until_lcd_on = i;
            printf("\n  [%6d] LCD turned ON\n", i);
            printf("             LCD mode: %d\n", dut->dbg_lcd_mode);
        }
        
        // Monitor vsync
        if (dut->dbg_lcd_vsync && !last_vsync) {
            vsync_count++;
            if (vsync_count <= 3) {
                printf("  [%6d] VSYNC %d - LCD_on=%d mode=%d\n", 
                       i, vsync_count, dut->dbg_lcd_on, dut->dbg_lcd_mode);
            }
        }
        last_vsync = dut->dbg_lcd_vsync;
        
        // Monitor pixel output (lcd_clkena indicates valid pixel)
        if (dut->dbg_lcd_clkena) {
            lcd_pixels_output++;
            
            // Check lcd_data_gb for GameBoy 2-bit color
            uint8_t pixel = dut->dbg_lcd_data_gb;
            
            if (pixel != 0) {
                nonzero_pixels++;
                
                if (nonzero_pixels == 1) {
                    first_nonzero_pixel = pixel;
                    first_pixel_cycle = i;
                    cycles_until_first_pixel = i;
                    printf("\n  [%6d] First non-zero pixel: $%02X\n", i, pixel);
                    printf("             LCD data (15-bit): $%04X\n", dut->dbg_lcd_data);
                }
                
                if (nonzero_pixels <= 10) {
                    printf("  [%6d] Pixel #%d: value=$%02X lcd_data=$%04X\n",
                           i, nonzero_pixels, pixel, dut->dbg_lcd_data);
                }
            }
        }
        
        // Stop after 3 vsyncs or if we've seen pixels
        if (vsync_count >= 3 && nonzero_pixels > 100) {
            break;
        }
    }
    
    printf("\n--- Results ---\n");
    printf("VRAM writes: %d\n", vram_writes);
    printf("LCD turned on: %s (cycle %d)\n", lcd_turned_on ? "YES" : "NO", cycles_until_lcd_on);
    printf("VSync count: %d\n", vsync_count);
    printf("Total pixel clocks: %d\n", lcd_pixels_output);
    printf("Non-zero pixels: %d\n", nonzero_pixels);
    
    if (cycles_until_first_pixel >= 0) {
        printf("First pixel at cycle: %d\n", cycles_until_first_pixel);
        printf("First pixel value: $%02X\n", first_nonzero_pixel);
    }
    
    printf("\n--- Analysis ---\n");
    
    if (vram_writes == 0) {
        printf("✗ No VRAM writes - boot ROM not executing\n");
    } else {
        printf("✓ VRAM writes occurred (%d total)\n", vram_writes);
    }
    
    if (!lcd_turned_on) {
        printf("✗ LCD never turned on - check LCDC register\n");
    } else {
        printf("✓ LCD enabled\n");
    }
    
    if (vsync_count == 0) {
        printf("✗ No VSYNC signals - video timing not working\n");
    } else {
        printf("✓ VSYNC working (%d frames)\n", vsync_count);
    }
    
    if (lcd_pixels_output == 0) {
        printf("✗ No pixel clock enables - LCD controller not outputting\n");
    } else {
        printf("✓ LCD outputting pixels (%d clocks)\n", lcd_pixels_output);
    }
    
    if (nonzero_pixels == 0) {
        printf("✗ All pixels are zero (blank screen)\n");
        printf("  Possible causes:\n");
        printf("  - VRAM not being read by video controller\n");
        printf("  - Tile/sprite data not decoded\n");
        printf("  - Background/window disabled\n");
        printf("  - Wrong palette mapping (all white)\n");
    } else {
        printf("✓ Non-zero pixels detected (%d pixels)\n", nonzero_pixels);
        printf("  Display appears to be working!\n");
    }
    
    delete sdram;
    delete dut;
    return (nonzero_pixels > 0) ? 0 : 1;
}
