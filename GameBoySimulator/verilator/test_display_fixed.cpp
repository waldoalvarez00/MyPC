// GameBoy RTL - Display Test with Correct Boot Sequence
// Key insight: dn_write only pulses when ce_cpu is running!
// So reset must be released BEFORE or DURING download for cart_ready to set.

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "../sim/mister_sdram_model.h"
#include "display_test_rom.h"

Vtop* top = nullptr;
MisterSDRAMModel* sdram = nullptr;
vluint64_t main_time = 0;
int clk = 0;

void processSDRAM() {
    uint16_t rdata = 0;
    bool compl_out = false;
    bool config_done = false;

    sdram->processNativeSDRAM(
        top->sd_cs, top->sd_ras, top->sd_cas, top->sd_we,
        top->sd_ba, top->sd_addr, top->sd_data_out, top->sd_dqm,
        rdata, compl_out, config_done
    );
    top->sd_data_in = rdata;
}

void tick() {
    clk = !clk;
    top->clk_sys = clk;
    top->eval();
    if (clk) {
        processSDRAM();
        main_time++;
    }
}

int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("Display Test (ce_cpu aware boot)\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);
    top = new Vtop();
    sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;  // Realistic CAS latency
    sdram->debug = false;

    auto* root = top->rootp;

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

    // Step 1: Brief reset to initialize SDRAM controller
    printf("Step 1: Initial reset...\n");
    for (int i = 0; i < 100; i++) {
        tick();
    }

    // Step 2: Load ROM to SDRAM model (fast path)
    printf("Step 2: Loading ROM to SDRAM (%zu bytes)...\n", sizeof(display_test_rom));
    for (size_t addr = 0; addr < sizeof(display_test_rom); addr += 2) {
        uint16_t word = display_test_rom[addr];
        if (addr + 1 < sizeof(display_test_rom)) {
            word |= (display_test_rom[addr + 1] << 8);
        }
        sdram->write16(addr, word);
    }

    // Step 3: Release reset FIRST so ce_cpu starts running
    printf("Step 3: Releasing reset so ce_cpu runs...\n");
    top->reset = 0;

    // Disable boot ROM
    for (int i = 0; i < 100; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // Let SDRAM init complete
    printf("  Running SDRAM init cycles...\n");
    for (int i = 0; i < 2000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }
    printf("  SDRAM refreshes: %lu\n", (unsigned long)sdram->refresh_count);

    // Step 4: NOW do download - ce_cpu is running so dn_write will pulse
    printf("Step 4: Simulating ioctl download (ce_cpu is running)...\n");
    top->ioctl_download = 1;
    top->ioctl_index = 0;

    for (size_t addr = 0; addr < sizeof(display_test_rom); addr += 2) {
        // Keep boot ROM disabled during download
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

        uint16_t word = display_test_rom[addr];
        if (addr + 1 < sizeof(display_test_rom)) {
            word |= (display_test_rom[addr + 1] << 8);
        }
        top->ioctl_dout = word;
        top->ioctl_addr = addr >> 1;
        top->ioctl_wr = 1;

        // Need more cycles per word to let ce_cpu pulse and process
        for (int i = 0; i < 32; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }
        top->ioctl_wr = 0;
        for (int i = 0; i < 32; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }

        if ((addr % 0x4000) == 0 && addr > 0) {
            printf("  Downloaded %zu / %zu bytes, cart_ready=%d\n",
                   addr, sizeof(display_test_rom), top->dbg_cart_ready);
        }
    }
    top->ioctl_download = 0;

    // Run more cycles to let cart_ready propagate
    for (int i = 0; i < 1000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    printf("  Download complete. cart_ready=%d\n", top->dbg_cart_ready);

    if (!top->dbg_cart_ready) {
        printf("\n!!! WARNING: cart_ready is still 0! dn_write may not have pulsed.\n");
        printf("    Check if ce_cpu is running during download.\n\n");
    }

    // Step 5: Now reset the CPU to start fresh from 0x0000
    printf("Step 5: Pulsing reset to restart CPU at 0x0000...\n");
    top->reset = 1;
    for (int i = 0; i < 100; i++) {
        tick();
    }
    top->reset = 0;

    // Disable boot ROM again
    for (int i = 0; i < 100; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    printf("  cart_ready after reset: %d\n", top->dbg_cart_ready);

    // Step 6: Trace CPU execution
    printf("\nStep 6: Tracing first 50 CPU cycles:\n");
    int traced = 0;
    uint16_t last_addr = 0;
    uint16_t max_addr = 0;

    for (int i = 0; i < 10000 && traced < 50; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();

        if (top->dbg_ce_cpu) {
            traced++;
            uint16_t addr = top->dbg_cpu_addr;
            printf("  [%3d] addr=0x%04X rd_n=%d cart_rd=%d cart_ready=%d\n",
                   traced, addr, top->dbg_cpu_rd_n, top->dbg_cart_rd, top->dbg_cart_ready);

            if (addr > max_addr) max_addr = addr;
            last_addr = addr;
        }
    }

    printf("\n  After first 50 cycles: max_addr=0x%04X\n", max_addr);

    // Step 7: Run for longer
    printf("\nStep 7: Running for 1M more cycles...\n");
    int addr_changes = 0;
    int lcd_on_cycles = 0;
    int mode3_cycles = 0;
    int nonzero_pixels = 0;

    for (int i = 0; i < 1000000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();

        uint16_t addr = top->dbg_cpu_addr;
        if (addr != last_addr) {
            addr_changes++;
            last_addr = addr;
            if (addr > max_addr) max_addr = addr;
        }

        if (top->dbg_lcd_on) lcd_on_cycles++;
        if (top->dbg_lcd_mode == 3) {
            mode3_cycles++;
            if (top->VGA_R || top->VGA_G || top->VGA_B) nonzero_pixels++;
        }

        if (i % 200000 == 0 && i > 0) {
            uint8_t lcdc = root->top__DOT__gameboy__DOT__video__DOT__lcdc;
            printf("  %d cycles: addr=0x%04X max=0x%04X LCDC=0x%02X lcd_on=%d pixels=%d\n",
                   i, last_addr, max_addr, lcdc, top->dbg_lcd_on, nonzero_pixels);
        }
    }

    printf("\n=== Final Results ===\n");
    printf("Max address reached: 0x%04X\n", max_addr);
    printf("Final address: 0x%04X\n", last_addr);
    printf("Address changes: %d\n", addr_changes);
    printf("LCD on cycles: %d\n", lcd_on_cycles);
    printf("Mode 3 cycles: %d\n", mode3_cycles);
    printf("Nonzero pixels: %d\n", nonzero_pixels);

    uint8_t lcdc = root->top__DOT__gameboy__DOT__video__DOT__lcdc;
    printf("LCDC: 0x%02X (LCD enable=%d)\n", lcdc, (lcdc >> 7) & 1);

    // Cleanup
    top->final();
    delete top;
    delete sdram;

    if (nonzero_pixels > 0) {
        printf("\n=== SUCCESS: Display ROM produces visible pixels! ===\n");
        return 0;
    } else if (lcd_on_cycles > 0) {
        printf("\n=== PARTIAL: LCD enabled but no visible pixels ===\n");
        return 0;
    } else if (max_addr >= 0x0150) {
        printf("\n=== PARTIAL: ROM code reached but LCD not on ===\n");
        return 0;
    } else if (max_addr >= 0x0100) {
        printf("\n=== PARTIAL: Reached cart entry but not main code ===\n");
        return 0;
    } else {
        printf("\n=== ISSUE: CPU stuck before cart entry (0x0100) ===\n");
        return 1;
    }
}
