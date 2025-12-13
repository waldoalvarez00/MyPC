// GameBoy RTL Unit Test - Common Utilities
// Shared infrastructure for all GameBoy unit tests

#ifndef GB_TEST_COMMON_H
#define GB_TEST_COMMON_H

#include <verilated.h>
#include <cstdio>
#include <cstdint>
#include <cstring>

// Include SDRAM model for tests that need memory
#include "../sim/mister_sdram_model.h"

//=============================================================================
// Test Result Tracking
//=============================================================================
struct TestResults {
    int total = 0;
    int passed = 0;
    int failed = 0;
    const char* current_suite = "Unknown";

    void set_suite(const char* name) {
        current_suite = name;
        printf("\n=== %s ===\n", name);
    }

    void check(bool condition, const char* name) {
        total++;
        if (condition) {
            passed++;
            printf("  [PASS] %s\n", name);
        } else {
            failed++;
            printf("  [FAIL] %s\n", name);
        }
    }

    void check_eq(uint32_t actual, uint32_t expected, const char* name) {
        total++;
        if (actual == expected) {
            passed++;
            printf("  [PASS] %s (0x%X)\n", name, actual);
        } else {
            failed++;
            printf("  [FAIL] %s: expected 0x%X, got 0x%X\n", name, expected, actual);
        }
    }

    void check_ne(uint32_t actual, uint32_t not_expected, const char* name) {
        total++;
        if (actual != not_expected) {
            passed++;
            printf("  [PASS] %s (0x%X != 0x%X)\n", name, actual, not_expected);
        } else {
            failed++;
            printf("  [FAIL] %s: got unexpected value 0x%X\n", name, actual);
        }
    }

    int report() {
        printf("\n");
        printf("==========================================\n");
        printf("TEST RESULTS: %s\n", current_suite);
        printf("==========================================\n");
        printf("Tests: %d, Pass: %d, Fail: %d\n", total, passed, failed);
        if (failed == 0) {
            printf("=== ALL TESTS PASSED ===\n");
        } else {
            printf("=== %d TESTS FAILED ===\n", failed);
        }
        return (failed == 0) ? 0 : 1;
    }
};

//=============================================================================
// Clock and Simulation Helpers
//=============================================================================

// Single clock cycle (rising + falling edge)
template<typename T>
void tick(T* dut) {
    dut->clk_sys = 1;
    dut->eval();
    dut->clk_sys = 0;
    dut->eval();
}

// Run N clock cycles
template<typename T>
void run_cycles(T* dut, int n) {
    for (int i = 0; i < n; i++) {
        tick(dut);
    }
}

// Run cycles with SDRAM model
template<typename T>
void tick_with_sdram(T* dut, MisterSDRAMModel* sdram) {
    dut->clk_sys = 1;
    dut->eval();

    // Process SDRAM on rising edge
    // Hold last SDRAM read data on the bus until the model updates it.
    // The SDRAM model intentionally doesn't clear rdata every cycle, but if we
    // reinitialize here we effectively drive 0x0000 between valid beats.
    uint16_t rdata = dut->sd_data_in;
    bool compl_out = false;
    bool config_done = false;

    sdram->processNativeSDRAM(
        dut->sd_cs,
        dut->sd_ras,
        dut->sd_cas,
        dut->sd_we,
        dut->sd_ba,
        dut->sd_addr,
        dut->sd_data_out,
        dut->sd_dqm,
        rdata,
        compl_out,
        config_done
    );
    dut->sd_data_in = rdata;

    dut->clk_sys = 0;
    dut->eval();
}

template<typename T>
void run_cycles_with_sdram(T* dut, MisterSDRAMModel* sdram, int n) {
    for (int i = 0; i < n; i++) {
        tick_with_sdram(dut, sdram);
    }
}

//=============================================================================
// Reset Helper
//=============================================================================
template<typename T>
void reset_dut(T* dut, int cycles = 100) {
    dut->reset = 1;
    dut->inputs = 0xFF;  // All buttons released
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;

    run_cycles(dut, cycles);

    dut->reset = 0;
}

template<typename T>
void reset_dut_with_sdram(T* dut, MisterSDRAMModel* sdram, int cycles = 100) {
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;

    run_cycles_with_sdram(dut, sdram, cycles);

    dut->reset = 0;
}

//=============================================================================
// Wait for condition helpers
//=============================================================================
template<typename T, typename F>
bool wait_for_condition(T* dut, F condition, int max_cycles, MisterSDRAMModel* sdram = nullptr) {
    for (int i = 0; i < max_cycles; i++) {
        if (sdram) {
            tick_with_sdram(dut, sdram);
        } else {
            tick(dut);
        }
        if (condition()) {
            return true;
        }
    }
    return false;
}

//=============================================================================
// Count signal transitions
//=============================================================================
template<typename T>
int count_signal_highs(T* dut, int (T::*signal), int cycles, MisterSDRAMModel* sdram = nullptr) {
    int count = 0;
    for (int i = 0; i < cycles; i++) {
        if (sdram) {
            tick_with_sdram(dut, sdram);
        } else {
            tick(dut);
        }
        if (dut->*signal) {
            count++;
        }
    }
    return count;
}

//=============================================================================
// Debug output helpers
//=============================================================================
template<typename T>
void print_debug_state(T* dut) {
    printf("  State: ce_cpu=%d cpu_clken=%d hdma_active=%d dma_rd=%d\n",
           dut->dbg_ce_cpu, dut->dbg_cpu_clken,
           dut->dbg_hdma_active, dut->dbg_dma_rd);
    printf("         cpu_addr=0x%04X cpu_rd_n=%d cart_rd=%d\n",
           dut->dbg_cpu_addr, dut->dbg_cpu_rd_n, dut->dbg_cart_rd);
    printf("         boot_rom_enabled=%d sel_boot_rom=%d\n",
           dut->dbg_boot_rom_enabled, dut->dbg_sel_boot_rom);
}

//=============================================================================
// LCD Control Helper
// Enables the LCD by setting LCDC bit 7 (required for LCD modes to cycle)
//
// NOTE: Verilator's internal member layout can change (flattening vs submodules).
// Access the reg via the generated module hierarchy pointers instead of relying
// on flattened member names.
//=============================================================================
#include "Vtop___024root.h"
#include "Vtop_top.h"
#include "Vtop_gb.h"
#include "Vtop_video.h"

template<typename T>
void enable_lcd(T* dut) {
    auto* root = dut->rootp;
    // top module is `Vtop_top`, which contains `gameboy` (gb), which contains `video`.
    root->top->gameboy->video->__PVT__lcdc = 0x91;  // LCD on, BG enabled, OBJ enabled
}

template<typename T>
void disable_lcd(T* dut) {
    auto* root = dut->rootp;
    root->top->gameboy->video->__PVT__lcdc = 0x00;  // LCD off
}

#endif // GB_TEST_COMMON_H
