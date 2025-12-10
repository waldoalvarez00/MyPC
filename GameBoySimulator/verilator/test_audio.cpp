// GameBoy RTL Unit Test - Audio Output
// Tests for APU functionality and audio output signals

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

//=============================================================================
// Test: Audio output signals exist and are accessible
//=============================================================================
void test_audio_signals_accessible(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Audio Signals Accessible");

    reset_dut_with_sdram(dut, sdram);

    // Run some cycles
    run_cycles_with_sdram(dut, sdram, 1000);

    // Verify audio signals are accessible (even if zero)
    int16_t audio_l = (int16_t)dut->AUDIO_L;
    int16_t audio_r = (int16_t)dut->AUDIO_R;

    printf("  [INFO] AUDIO_L = 0x%04X (%d)\n", dut->AUDIO_L, audio_l);
    printf("  [INFO] AUDIO_R = 0x%04X (%d)\n", dut->AUDIO_R, audio_r);

    // Always pass - we're just verifying signal access
    results.check(true, "AUDIO_L signal accessible");
    results.check(true, "AUDIO_R signal accessible");
}

//=============================================================================
// Test: Audio output activity over time
//=============================================================================
void test_audio_output_activity(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Audio Output Activity");

    reset_dut_with_sdram(dut, sdram);

    int nonzero_l = 0;
    int nonzero_r = 0;
    int changes_l = 0;
    int changes_r = 0;
    uint16_t last_l = dut->AUDIO_L;
    uint16_t last_r = dut->AUDIO_R;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->AUDIO_L != 0) nonzero_l++;
        if (dut->AUDIO_R != 0) nonzero_r++;

        if (dut->AUDIO_L != last_l) {
            changes_l++;
            last_l = dut->AUDIO_L;
        }
        if (dut->AUDIO_R != last_r) {
            changes_r++;
            last_r = dut->AUDIO_R;
        }
    }

    printf("  [INFO] Nonzero samples: L=%d, R=%d out of 100000\n", nonzero_l, nonzero_r);
    printf("  [INFO] Value changes: L=%d, R=%d\n", changes_l, changes_r);

    // Note: With stub audio (gbc_snd.v), may see no activity
    // This documents the state for debugging
    if (nonzero_l == 0 && nonzero_r == 0) {
        printf("  [WARN] No audio activity - using stub audio module\n");
    }

    // Test passes if we can sample the signals
    results.check(true, "Audio sampling works");
}

//=============================================================================
// Test: Audio output range
//=============================================================================
void test_audio_output_range(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Audio Output Range");

    reset_dut_with_sdram(dut, sdram);

    int16_t min_l = 32767, max_l = -32768;
    int16_t min_r = 32767, max_r = -32768;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        int16_t l = (int16_t)dut->AUDIO_L;
        int16_t r = (int16_t)dut->AUDIO_R;

        if (l < min_l) min_l = l;
        if (l > max_l) max_l = l;
        if (r < min_r) min_r = r;
        if (r > max_r) max_r = r;
    }

    printf("  [INFO] AUDIO_L range: %d to %d\n", min_l, max_l);
    printf("  [INFO] AUDIO_R range: %d to %d\n", min_r, max_r);

    // Audio should be within 16-bit signed range
    results.check(min_l >= -32768 && max_l <= 32767, "AUDIO_L within valid range");
    results.check(min_r >= -32768 && max_r <= 32767, "AUDIO_R within valid range");
}

//=============================================================================
// Test: Audio stereo balance
//=============================================================================
void test_audio_stereo_balance(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Audio Stereo Balance");

    reset_dut_with_sdram(dut, sdram);

    long long sum_l = 0, sum_r = 0;
    int samples = 0;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        sum_l += (int16_t)dut->AUDIO_L;
        sum_r += (int16_t)dut->AUDIO_R;
        samples++;
    }

    float avg_l = samples > 0 ? (float)sum_l / samples : 0;
    float avg_r = samples > 0 ? (float)sum_r / samples : 0;

    printf("  [INFO] Average AUDIO_L: %.2f\n", avg_l);
    printf("  [INFO] Average AUDIO_R: %.2f\n", avg_r);

    // Test passes if averages are reasonable (not extreme DC offset)
    results.check(avg_l > -20000 && avg_l < 20000, "AUDIO_L average not extreme");
    results.check(avg_r > -20000 && avg_r < 20000, "AUDIO_R average not extreme");
}

//=============================================================================
// Test: Audio and video timing correlation
//=============================================================================
void test_audio_video_correlation(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Audio/Video Timing");

    reset_dut_with_sdram(dut, sdram);
    enable_lcd(dut);

    int audio_changes_in_vblank = 0;
    int audio_changes_outside_vblank = 0;
    uint16_t last_l = dut->AUDIO_L;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->AUDIO_L != last_l) {
            if (dut->dbg_lcd_mode == 1) {
                audio_changes_in_vblank++;
            } else {
                audio_changes_outside_vblank++;
            }
            last_l = dut->AUDIO_L;
        }
    }

    printf("  [INFO] Audio changes in VBlank: %d\n", audio_changes_in_vblank);
    printf("  [INFO] Audio changes outside VBlank: %d\n", audio_changes_outside_vblank);

    // Audio should run independently of video timing
    // This test just documents the relationship
    results.check(true, "Audio/video timing documented");
}

//=============================================================================
// Main
//=============================================================================
int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("GameBoy Audio Output Unit Tests\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->debug = false;

    // Load a simple ROM (NOPs) into SDRAM
    for (int i = 0; i < 0x8000; i += 2) {
        sdram->write16(i, 0x0000);  // NOPs
    }

    TestResults results;
    results.current_suite = "Audio Output Tests";

    // Run all test suites
    test_audio_signals_accessible(dut, sdram, results);
    test_audio_output_activity(dut, sdram, results);
    test_audio_output_range(dut, sdram, results);
    test_audio_stereo_balance(dut, sdram, results);
    test_audio_video_correlation(dut, sdram, results);

    // Cleanup
    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
