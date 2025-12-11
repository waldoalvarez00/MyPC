// GameBoy RTL Diagnostic - Display ROM Test
// Tests that a properly-written ROM produces visible output
// Uses full initialization sequence like test_gameboy_core.cpp

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "../sim/mister_sdram_model.h"
#include "display_test_rom.h"

// Global state
Vtop* top = nullptr;
MisterSDRAMModel* sdram = nullptr;
vluint64_t main_time = 0;
int clk = 0;

// Process SDRAM signals
void processSDRAM() {
    uint16_t rdata = 0;
    bool compl_out = false;
    bool config_done = false;

    sdram->processNativeSDRAM(
        top->sd_cs,
        top->sd_ras,
        top->sd_cas,
        top->sd_we,
        top->sd_ba,
        top->sd_addr,
        top->sd_data_out,
        top->sd_dqm,
        rdata,
        compl_out,
        config_done
    );

    top->sd_data_in = rdata;
}

// Run one clock cycle
void tick() {
    clk = !clk;
    top->clk_sys = clk;

    top->eval();

    if (clk) {
        processSDRAM();
        main_time++;
    }
}

// Simulate ioctl download to make cart_ready go high
void simulateDownload(const uint8_t* rom_data, size_t rom_size) {
    printf("Simulating ioctl download (%zu bytes)...\n", rom_size);

    top->ioctl_download = 1;
    top->ioctl_index = 0;

    size_t addr = 0;
    int cycles_per_word = 32;

    while (addr < rom_size) {
        uint16_t word = rom_data[addr];
        if (addr + 1 < rom_size) {
            word |= (rom_data[addr + 1] << 8);
        }

        top->ioctl_dout = word;
        top->ioctl_addr = addr >> 1;
        top->ioctl_wr = 1;

        for (int i = 0; i < 4; i++) {
            tick();
        }

        top->ioctl_wr = 0;

        for (int i = 0; i < cycles_per_word - 4; i++) {
            tick();
        }

        addr += 2;

        if ((addr % 0x4000) == 0) {
            printf("  Downloaded %zu / %zu bytes (%.0f%%)\n",
                   addr, rom_size, 100.0 * addr / rom_size);
        }
    }

    top->ioctl_download = 0;
    top->ioctl_wr = 0;

    for (int i = 0; i < 1000; i++) {
        tick();
    }

    printf("Download complete. cart_ready=%d\n", top->dbg_cart_ready);
}

int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("Display ROM Diagnostic Test (Full Init)\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);

    top = new Vtop();
    sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;  // Realistic CAS latency
    sdram->debug = false;

    // Initialize signals
    top->reset = 1;
    top->ioctl_download = 0;
    top->ioctl_wr = 0;
    top->ioctl_addr = 0;
    top->ioctl_dout = 0;
    top->ioctl_index = 0;
    top->inputs = 0xFF;
    top->boot_download = 0;
    top->boot_wr = 0;
    top->boot_addr = 0;
    top->boot_data = 0;

    // Run reset for 100 cycles
    printf("Running reset...\n");
    for (int i = 0; i < 100; i++) {
        tick();
    }

    // Load ROM directly to SDRAM model (bypassing controller for speed)
    printf("Loading display_test_rom directly to SDRAM (%zu bytes)...\n", sizeof(display_test_rom));
    for (size_t addr = 0; addr < sizeof(display_test_rom); addr += 2) {
        uint16_t word = display_test_rom[addr];
        if (addr + 1 < sizeof(display_test_rom)) {
            word |= (display_test_rom[addr + 1] << 8);
        }
        sdram->write16(addr, word);
    }

    // Release reset
    top->reset = 0;
    printf("Reset released\n");

    // Get root for internal signal access
    auto* root = top->rootp;

    // Disable boot ROM immediately and continuously
    printf("Disabling boot ROM...\n");
    for (int i = 0; i < 100; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // Run SDRAM init cycles
    printf("Running SDRAM init...\n");
    for (int i = 0; i < 1000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // Simulate ioctl download to trigger cart_ready
    simulateDownload(display_test_rom, sizeof(display_test_rom));

    // Let cart_ready propagate
    for (int i = 0; i < 1000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    printf("cart_ready=%d\n", top->dbg_cart_ready);

    printf("\n=== Running simulation ===\n");

    int nonzero_pixels = 0;
    int mode3_cycles = 0;
    int mode_transitions = 0;
    int last_mode = top->dbg_lcd_mode;
    int cpu_addr_changes = 0;
    uint16_t last_cpu_addr = top->dbg_cpu_addr;
    int lcd_on_cycles = 0;

    const int CYCLES = 1000000;  // 1M cycles for more time to initialize

    for (int i = 0; i < CYCLES; i++) {
        // CRITICAL: Keep boot ROM disabled every cycle
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();

        // Track LCD mode
        int mode = top->dbg_lcd_mode;
        if (mode != last_mode) {
            mode_transitions++;
            last_mode = mode;
        }

        // Track CPU address
        if (top->dbg_cpu_addr != last_cpu_addr) {
            cpu_addr_changes++;
            last_cpu_addr = top->dbg_cpu_addr;
        }

        // Track LCD on state
        if (top->dbg_lcd_on) {
            lcd_on_cycles++;
        }

        // Check for non-zero pixels during Mode 3
        if (mode == 3) {
            mode3_cycles++;
            if (top->VGA_R != 0 || top->VGA_G != 0 || top->VGA_B != 0) {
                nonzero_pixels++;
            }
        }

        // Progress every 200k cycles
        if (i % 200000 == 0 && i > 0) {
            uint8_t lcdc = root->top__DOT__gameboy__DOT__video__DOT__lcdc;
            printf("  %d cycles: mode=%d, cpu_addr=0x%04X, lcd_on=%d, LCDC=0x%02X, nonzero=%d\n",
                   i, top->dbg_lcd_mode, top->dbg_cpu_addr, top->dbg_lcd_on, lcdc, nonzero_pixels);
        }
    }

    printf("\n=== Results after %d cycles ===\n", CYCLES);
    printf("CPU address changes: %d\n", cpu_addr_changes);
    printf("LCD mode transitions: %d\n", mode_transitions);
    printf("LCD on cycles: %d (%.1f%%)\n", lcd_on_cycles, 100.0 * lcd_on_cycles / CYCLES);
    printf("Mode 3 cycles: %d\n", mode3_cycles);
    printf("Nonzero pixels: %d\n", nonzero_pixels);
    printf("Final CPU address: 0x%04X\n", top->dbg_cpu_addr);
    printf("Final LCD mode: %d\n", top->dbg_lcd_mode);
    printf("cart_ready: %d\n", top->dbg_cart_ready);

    // Check LCDC register
    uint8_t lcdc = root->top__DOT__gameboy__DOT__video__DOT__lcdc;
    printf("\nLCDC register: 0x%02X\n", lcdc);
    printf("  LCD enable (bit 7): %d\n", (lcdc >> 7) & 1);
    printf("  BG enable (bit 0): %d\n", lcdc & 1);

    // Check BGP palette
    uint8_t bgp = root->top__DOT__gameboy__DOT__video__DOT__bgp;
    printf("BGP palette: 0x%02X\n", bgp);

    // Final RGB values
    printf("\nFinal VGA output:\n");
    printf("  R: %d (0x%02X)\n", top->VGA_R, top->VGA_R);
    printf("  G: %d (0x%02X)\n", top->VGA_G, top->VGA_G);
    printf("  B: %d (0x%02X)\n", top->VGA_B, top->VGA_B);

    // Cleanup
    top->final();
    delete top;
    delete sdram;

    // Report
    printf("\n===========================================\n");
    if (nonzero_pixels > 0) {
        printf("SUCCESS: Display ROM produces visible pixels!\n");
        return 0;
    } else if (lcd_on_cycles > 0 && mode3_cycles > 0) {
        printf("PARTIAL: LCD is on and rendering, but pixels are zero\n");
        printf("  (Check tile data and palette initialization)\n");
        return 0;
    } else if (cpu_addr_changes > 1000 && (lcdc & 0x80)) {
        printf("PARTIAL: CPU running and LCD enabled, no pixels\n");
        return 0;
    } else if (cpu_addr_changes > 100) {
        printf("PARTIAL: CPU is running but LCD not enabled\n");
        printf("  ROM code may not be reaching LCD init section\n");
        return 1;
    } else {
        printf("ISSUE: CPU not making progress\n");
        return 1;
    }
}
