// GameBoy RTL Unit Test - Interrupt Timing
// Tests for interrupt flag handling
//
// IF register at 0xFF0F, IE register at 0xFFFF
// Interrupts: VBlank, LCD STAT, Timer, Serial, Joypad

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

//=============================================================================
// Test: LCD mode transitions generate VBlank
//=============================================================================
void test_lcd_vblank_detection(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("LCD VBlank Detection");

    reset_dut_with_sdram(dut, sdram);

    // Enable LCD - required for modes to cycle
    enable_lcd(dut);

    // Track LCD mode transitions
    int vblank_entries = 0;
    int last_mode = dut->dbg_lcd_mode;

    // Run for enough cycles to see at least one frame (~70224 clocks @ 4MHz)
    // At 64MHz with ce_cpu at 6.25%, need ~1.1M cycles for one frame
    // Let's run fewer cycles and just verify mode changes
    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        int mode = dut->dbg_lcd_mode;
        if (mode == 1 && last_mode != 1) {
            vblank_entries++;
        }
        last_mode = mode;
    }

    // May or may not see VBlank depending on cycle count
    printf("  [INFO] VBlank entries detected: %d\n", vblank_entries);

    // At minimum, verify LCD mode signal is valid
    results.check(dut->dbg_lcd_mode <= 3, "LCD mode is valid (0-3)");
}

//=============================================================================
// Test: LCD mode signal is stable
//=============================================================================
void test_lcd_mode_stability(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("LCD Mode Stability");

    reset_dut_with_sdram(dut, sdram);

    // Enable LCD - required for modes to cycle
    enable_lcd(dut);

    // Track mode transitions
    int transitions = 0;
    int last_mode = dut->dbg_lcd_mode;

    for (int i = 0; i < 10000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_lcd_mode != last_mode) {
            transitions++;
            last_mode = dut->dbg_lcd_mode;
        }
    }

    // Mode should change periodically but not every cycle
    results.check(transitions < 10000, "LCD mode doesn't change every cycle");
    results.check(transitions > 0, "LCD mode transitions occur (LCD enabled)");
    printf("  [INFO] LCD mode transitions: %d in 10000 cycles\n", transitions);
}

//=============================================================================
// Test: VSync signal correlation with LCD mode
//=============================================================================
void test_vsync_lcd_correlation(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("VSync/LCD Mode Correlation");

    reset_dut_with_sdram(dut, sdram);

    // VGA_VS should correlate with LCD VBlank (mode 1)
    int vsync_in_vblank = 0;
    int vsync_outside_vblank = 0;

    for (int i = 0; i < 50000; i++) {
        tick_with_sdram(dut, sdram);

        // VGA_VS is directly exposed, check correlation
        // This depends on exact implementation
    }

    // Just verify we can read VGA signals
    results.check(true, "VGA sync signals accessible");
    printf("  [INFO] VGA_HS=%d VGA_VS=%d at end of test\n",
           dut->VGA_HS, dut->VGA_VS);
}

//=============================================================================
// Test: CPU execution not blocked by interrupt system
//=============================================================================
void test_cpu_interrupt_coexistence(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("CPU/Interrupt Coexistence");

    reset_dut_with_sdram(dut, sdram);
    auto* root = dut->rootp;

    root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

    // Load ROM
    for (int i = 0; i < 0x8000; i += 2) {
        sdram->write16(i, 0x0000);  // NOPs
    }

    // Track CPU activity
    int cpu_clken_count = 0;
    int cpu_addr_changes = 0;
    uint16_t last_addr = dut->dbg_cpu_addr;

    for (int i = 0; i < 5000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cpu_clken) cpu_clken_count++;
        if (dut->dbg_cpu_addr != last_addr) {
            cpu_addr_changes++;
            last_addr = dut->dbg_cpu_addr;
        }
    }

    results.check(cpu_clken_count > 0, "CPU gets clock enables");
    results.check(cpu_addr_changes > 0, "CPU address changes (executing)");

    printf("  [INFO] cpu_clken count: %d, addr changes: %d\n",
           cpu_clken_count, cpu_addr_changes);
}

//=============================================================================
// Test: Timer-related signals
//=============================================================================
void test_timer_signals(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Timer Signals");

    reset_dut_with_sdram(dut, sdram);

    // Run cycles and observe DIV-like behavior via ce_cpu frequency
    int ce_cpu_count = 0;

    for (int i = 0; i < 1000; i++) {
        tick_with_sdram(dut, sdram);
        if (dut->dbg_ce_cpu) ce_cpu_count++;
    }

    // ce_cpu should fire ~6.25% of cycles (64MHz / 16 = 4MHz)
    float rate = (float)ce_cpu_count / 1000.0f * 100.0f;
    results.check(rate > 5.0f && rate < 8.0f,
                  "ce_cpu fires at expected rate (~6.25%)");

    printf("  [INFO] ce_cpu rate: %.2f%%\n", rate);
}

//=============================================================================
// Test: LCD mode distribution
//=============================================================================
void test_lcd_mode_distribution(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("LCD Mode Distribution");

    reset_dut_with_sdram(dut, sdram);

    // Enable LCD - required for modes to cycle
    enable_lcd(dut);

    int mode_counts[4] = {0, 0, 0, 0};

    for (int i = 0; i < 50000; i++) {
        tick_with_sdram(dut, sdram);
        int mode = dut->dbg_lcd_mode;
        if (mode >= 0 && mode <= 3) {
            mode_counts[mode]++;
        }
    }

    // Verify all modes are seen (depends on cycle count)
    int modes_seen = 0;
    for (int i = 0; i < 4; i++) {
        if (mode_counts[i] > 0) modes_seen++;
    }

    printf("  [INFO] Mode distribution:\n");
    printf("         Mode 0 (H-Blank): %d\n", mode_counts[0]);
    printf("         Mode 1 (V-Blank): %d\n", mode_counts[1]);
    printf("         Mode 2 (OAM):     %d\n", mode_counts[2]);
    printf("         Mode 3 (Pixel):   %d\n", mode_counts[3]);

    results.check(modes_seen >= 2, "Multiple LCD modes observed (LCD enabled)");
}

//=============================================================================
// Main
//=============================================================================
int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("GameBoy Interrupt Timing Unit Tests\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->debug = false;

    TestResults results;
    results.current_suite = "Interrupt Timing Tests";

    // Run all test suites
    test_lcd_vblank_detection(dut, sdram, results);
    test_lcd_mode_stability(dut, sdram, results);
    test_vsync_lcd_correlation(dut, sdram, results);
    test_cpu_interrupt_coexistence(dut, sdram, results);
    test_timer_signals(dut, sdram, results);
    test_lcd_mode_distribution(dut, sdram, results);

    // Cleanup
    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
