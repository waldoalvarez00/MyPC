// GameBoy RTL Diagnostic - Reset Behavior Debug
// Investigates why CPU starts at 0x2019 instead of 0x0000

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
    printf("Reset Behavior Debug Test\n");
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

    // Step 1: Initial reset
    printf("\nStep 1: Initial reset (100 cycles)...\n");
    for (int i = 0; i < 100; i++) {
        tick();
    }

    // Step 2: Load ROM to SDRAM
    printf("Step 2: Loading ROM to SDRAM (%zu bytes)...\n", sizeof(display_test_rom));
    for (size_t addr = 0; addr < sizeof(display_test_rom); addr += 2) {
        uint16_t word = display_test_rom[addr];
        if (addr + 1 < sizeof(display_test_rom)) {
            word |= (display_test_rom[addr + 1] << 8);
        }
        sdram->write16(addr, word);
    }

    // Step 3: Release reset
    printf("\nStep 3: Releasing reset...\n");
    printf("  boot_rom_enabled before release: %d\n", root->top__DOT__gameboy__DOT__boot_rom_enabled);

    top->reset = 0;

    // CRITICAL: Force boot_rom_enabled to 0 IMMEDIATELY on same clock
    // This must happen BEFORE the first CPU cycle after reset
    root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

    printf("  Tracing first 20 cycles after reset release...\n");

    for (int i = 0; i < 20; i++) {
        // Force boot_rom_enabled = 0 EVERY CYCLE
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();

        uint16_t addr = top->dbg_cpu_addr;
        uint8_t boot_en = root->top__DOT__gameboy__DOT__boot_rom_enabled;
        uint8_t sel_boot = root->top__DOT__gameboy__DOT__sel_boot_rom;
        uint8_t ce = top->dbg_ce_cpu;

        if (ce) {
            printf("    [%2d] ce_cpu! addr=0x%04X boot_en=%d sel_boot=%d\n",
                   i, addr, boot_en, sel_boot);
        }
    }

    // Run SDRAM init
    printf("\nStep 4: Running SDRAM init (1000 cycles)...\n");
    for (int i = 0; i < 1000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // Simulate download
    printf("\nStep 5: Simulating download...\n");
    top->ioctl_download = 1;
    top->ioctl_index = 0;

    for (size_t addr = 0; addr < sizeof(display_test_rom); addr += 2) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

        uint16_t word = display_test_rom[addr];
        if (addr + 1 < sizeof(display_test_rom)) {
            word |= (display_test_rom[addr + 1] << 8);
        }
        top->ioctl_dout = word;
        top->ioctl_addr = addr >> 1;
        top->ioctl_wr = 1;
        for (int i = 0; i < 4; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }
        top->ioctl_wr = 0;
        for (int i = 0; i < 28; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }
    }
    top->ioctl_download = 0;

    for (int i = 0; i < 500; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    printf("  cart_ready=%d\n", top->dbg_cart_ready);

    // Step 6: Now test a clean reset with boot ROM continuously disabled
    printf("\n=== Step 6: Clean Reset Test ===\n");
    printf("Asserting reset WHILE keeping boot_rom_enabled=0...\n");

    top->reset = 1;
    for (int i = 0; i < 100; i++) {
        // Force boot_rom_enabled=0 even during reset
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    printf("Releasing reset with boot_rom_enabled continuously at 0...\n");
    top->reset = 0;

    // Trace first 50 CPU cycles
    int traced = 0;
    uint16_t first_addr = 0xFFFF;

    printf("\nFirst 50 CPU cycles (ce_cpu pulses):\n");
    for (int i = 0; i < 10000 && traced < 50; i++) {
        // Force boot_rom_enabled=0 EVERY cycle
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();

        if (top->dbg_ce_cpu) {
            traced++;
            uint16_t addr = top->dbg_cpu_addr;
            uint8_t boot_en = root->top__DOT__gameboy__DOT__boot_rom_enabled;
            uint8_t sel_boot = root->top__DOT__gameboy__DOT__sel_boot_rom;

            if (traced == 1) first_addr = addr;

            if (traced <= 20) {
                printf("  [%3d] addr=0x%04X boot_en=%d sel_boot=%d\n",
                       traced, addr, boot_en, sel_boot);
            }
        }
    }

    printf("\n  First address after reset: 0x%04X (expected 0x0000)\n", first_addr);

    // Continue running to check max address reached
    uint16_t max_addr = first_addr;
    uint16_t last_addr = first_addr;

    for (int i = 0; i < 500000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();

        if (top->dbg_ce_cpu) {
            uint16_t addr = top->dbg_cpu_addr;
            if (addr > max_addr) max_addr = addr;
            last_addr = addr;
        }
    }

    printf("\n=== Results ===\n");
    printf("First address: 0x%04X\n", first_addr);
    printf("Max address: 0x%04X\n", max_addr);
    printf("Final address: 0x%04X\n", last_addr);
    printf("cart_ready: %d\n", top->dbg_cart_ready);

    top->final();
    delete top;
    delete sdram;

    if (first_addr == 0x0000) {
        printf("\n=== SUCCESS: CPU starts at 0x0000 ===\n");
        return 0;
    } else {
        printf("\n=== ISSUE: CPU starts at 0x%04X instead of 0x0000 ===\n", first_addr);
        return 1;
    }
}
