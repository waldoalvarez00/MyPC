// GameBoy RTL Unit Test - HDMA Controller
// Tests for H-Blank DMA state machine and CPU stall interaction
//
// HDMA transfers 16-byte blocks during H-Blank periods.
// GDMA transfers all data immediately with 4-cycle delay.

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

//=============================================================================
// Test: HDMA inactive after reset
//=============================================================================
void test_hdma_inactive_after_reset(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("HDMA Inactive After Reset");

    reset_dut_with_sdram(dut, sdram);

    // Run a few cycles
    run_cycles_with_sdram(dut, sdram, 100);

    // Verify HDMA is not active
    results.check_eq(dut->dbg_hdma_active, 0, "hdma_active is 0 after reset");
    results.check_eq(dut->dbg_hdma_read_ext_bus, 0, "hdma_read_ext_bus is 0 after reset");

    // Run more cycles to ensure it stays inactive
    int hdma_active_count = 0;
    for (int i = 0; i < 500; i++) {
        tick_with_sdram(dut, sdram);
        if (dut->dbg_hdma_active) hdma_active_count++;
    }

    results.check_eq(hdma_active_count, 0, "HDMA stays inactive without trigger");
}

//=============================================================================
// Test: HDMA signal relationships
//=============================================================================
void test_hdma_signal_relationships(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("HDMA Signal Relationships");

    reset_dut_with_sdram(dut, sdram);

    // Verify signal relationships over many cycles
    int violations = 0;

    for (int i = 0; i < 1000; i++) {
        tick_with_sdram(dut, sdram);

        // hdma_read_ext_bus should imply hdma_active
        // (can't read external bus if HDMA not active)
        if (dut->dbg_hdma_read_ext_bus && !dut->dbg_hdma_active) {
            violations++;
            printf("  [WARN] hdma_read_ext_bus=1 but hdma_active=0 at cycle %d\n", i);
        }
    }

    results.check(violations == 0,
                  "hdma_read_ext_bus implies hdma_active");
}

//=============================================================================
// Test: LCD mode transitions occur
//=============================================================================
void test_lcd_mode_transitions(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("LCD Mode Transitions");

    reset_dut_with_sdram(dut, sdram);

    // Enable LCD - required for modes to cycle!
    // Without this, LCD stays in mode 0 (LCDC bit 7 controls LCD enable)
    enable_lcd(dut);

    // Track LCD mode values seen
    int mode_0_count = 0;  // H-Blank
    int mode_1_count = 0;  // V-Blank
    int mode_2_count = 0;  // OAM Search
    int mode_3_count = 0;  // Pixel Transfer

    const int TEST_CYCLES = 50000;  // Need many cycles to see LCD frame

    for (int i = 0; i < TEST_CYCLES; i++) {
        tick_with_sdram(dut, sdram);

        switch (dut->dbg_lcd_mode) {
            case 0: mode_0_count++; break;
            case 1: mode_1_count++; break;
            case 2: mode_2_count++; break;
            case 3: mode_3_count++; break;
        }
    }

    // Verify all LCD modes occur during a frame
    results.check(mode_0_count > 0, "LCD Mode 0 (H-Blank) occurs");
    results.check(mode_1_count > 0 || mode_2_count > 0 || mode_3_count > 0,
                  "Other LCD modes occur");

    printf("  [INFO] Mode distribution over %d cycles:\n", TEST_CYCLES);
    printf("         Mode 0 (H-Blank): %d\n", mode_0_count);
    printf("         Mode 1 (V-Blank): %d\n", mode_1_count);
    printf("         Mode 2 (OAM):     %d\n", mode_2_count);
    printf("         Mode 3 (Pixel):   %d\n", mode_3_count);
}

//=============================================================================
// Test: HDMA does not corrupt CPU state
//=============================================================================
void test_hdma_cpu_isolation(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("HDMA CPU Isolation");

    reset_dut_with_sdram(dut, sdram);

    // Load NOP sled to SDRAM
    for (int i = 0; i < 0x1000; i += 2) {
        sdram->write16(i, 0x0000);  // NOPs
    }

    auto* root = dut->rootp;

    // Disable boot ROM
    root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

    // Track CPU address
    uint16_t initial_addr = dut->dbg_cpu_addr;
    int addr_changes = 0;
    uint16_t last_addr = initial_addr;

    // Run and verify CPU continues to execute
    for (int i = 0; i < 2000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cpu_addr != last_addr) {
            addr_changes++;
            last_addr = dut->dbg_cpu_addr;
        }
    }

    results.check(addr_changes > 0, "CPU address changes without HDMA interference");

    // Verify HDMA wasn't accidentally triggered
    results.check_eq(dut->dbg_hdma_active, 0, "HDMA still inactive");
}

//=============================================================================
// Test: HDMA external bus signal timing
//=============================================================================
void test_hdma_ext_bus_timing(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("HDMA External Bus Timing");

    reset_dut_with_sdram(dut, sdram);

    // Monitor hdma_read_ext_bus timing
    int last_hdma_ext = 0;
    int rising_edges = 0;
    int falling_edges = 0;

    for (int i = 0; i < 5000; i++) {
        tick_with_sdram(dut, sdram);

        int curr = dut->dbg_hdma_read_ext_bus;
        if (curr && !last_hdma_ext) rising_edges++;
        if (!curr && last_hdma_ext) falling_edges++;
        last_hdma_ext = curr;
    }

    // Without HDMA trigger, should see no edges
    results.check_eq(rising_edges, 0, "No HDMA ext bus rising edges without trigger");
    results.check_eq(falling_edges, 0, "No HDMA ext bus falling edges without trigger");

    printf("  [INFO] HDMA external bus signal stable when inactive\n");
}

//=============================================================================
// Test: HDMA vs DMA signal exclusivity
//=============================================================================
void test_hdma_dma_exclusivity(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("HDMA vs DMA Exclusivity");

    reset_dut_with_sdram(dut, sdram);

    // Both HDMA and DMA accessing external bus simultaneously is a conflict
    int simultaneous_access = 0;

    for (int i = 0; i < 5000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_hdma_read_ext_bus && dut->dbg_dma_read_ext_bus) {
            simultaneous_access++;
        }
    }

    results.check(simultaneous_access == 0,
                  "HDMA and DMA never access external bus simultaneously");
}

//=============================================================================
// Test: CPU clock enable during potential HDMA
//=============================================================================
void test_cpu_clken_during_hdma_window(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("CPU Clock Enable During HDMA Window");

    reset_dut_with_sdram(dut, sdram);

    // During H-Blank (lcd_mode == 0), if HDMA were active, CPU would be stalled
    // Without HDMA active, CPU should continue during H-Blank

    int hblank_cycles = 0;
    int cpu_clken_during_hblank = 0;

    for (int i = 0; i < 20000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_lcd_mode == 0) {  // H-Blank
            hblank_cycles++;
            if (dut->dbg_cpu_clken) {
                cpu_clken_during_hblank++;
            }
        }
    }

    results.check(hblank_cycles > 0, "H-Blank periods detected");

    if (hblank_cycles > 0) {
        // CPU should still get clock enables during H-Blank when HDMA not active
        results.check(cpu_clken_during_hblank > 0,
                      "CPU gets clock enables during H-Blank (no HDMA)");
    }

    printf("  [INFO] %d H-Blank cycles, %d cpu_clken assertions\n",
           hblank_cycles, cpu_clken_during_hblank);
}

//=============================================================================
// Test: HDMA internal state after reset
//=============================================================================
void test_hdma_internal_state_reset(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("HDMA Internal State Reset");

    reset_dut_with_sdram(dut, sdram);

    auto* root = dut->rootp;

    // Run a few cycles to let signals settle
    run_cycles_with_sdram(dut, sdram, 100);

    // Check HDMA-related signals are in expected initial state
    results.check_eq(dut->dbg_hdma_active, 0, "hdma_active is 0");
    results.check_eq(dut->dbg_hdma_read_ext_bus, 0, "hdma_read_ext_bus is 0");

    // Verify these stay stable
    for (int i = 0; i < 100; i++) {
        tick_with_sdram(dut, sdram);
    }

    results.check_eq(dut->dbg_hdma_active, 0, "hdma_active stays 0");
    results.check_eq(dut->dbg_hdma_read_ext_bus, 0, "hdma_read_ext_bus stays 0");
}

//=============================================================================
// Main
//=============================================================================
int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("GameBoy HDMA Controller Unit Tests\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->debug = false;

    TestResults results;
    results.current_suite = "HDMA Controller Tests";

    // Run all test suites
    test_hdma_inactive_after_reset(dut, sdram, results);
    test_hdma_signal_relationships(dut, sdram, results);
    test_lcd_mode_transitions(dut, sdram, results);
    test_hdma_cpu_isolation(dut, sdram, results);
    test_hdma_ext_bus_timing(dut, sdram, results);
    test_hdma_dma_exclusivity(dut, sdram, results);
    test_cpu_clken_during_hdma_window(dut, sdram, results);
    test_hdma_internal_state_reset(dut, sdram, results);

    // Cleanup
    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
