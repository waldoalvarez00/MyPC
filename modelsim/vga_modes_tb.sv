// VGA Mode Definitions Testbench
// Tests VGATypes.sv mode parameter functions
//
// This validates that all 15 video modes have correct definitions

`timescale 1ns/1ps

`include "../Quartus/rtl/VGA/VGATypes.sv"

module vga_modes_tb;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// Test reporting
task report_test(input string name, input logic passed);
    begin
        test_count = test_count + 1;
        if (passed) begin
            $display("  [PASS] %s", name);
            pass_count = pass_count + 1;
        end else begin
            $display("  [FAIL] %s", name);
            fail_count = fail_count + 1;
        end
    end
endtask

// Test mode parameters
task test_mode(input VideoModeNumber_t mode_num,
               input string mode_name,
               input logic [10:0] exp_h_active,
               input logic [10:0] exp_v_active,
               input BitsPerPixel_t exp_bpp,
               input logic exp_is_text,
               input logic exp_is_graphics);
    begin
        VideoModeParams_t params;
        params = get_mode_params(mode_num);

        $display("");
        $display("Testing Mode %02Xh: %s", mode_num, mode_name);
        $display("  Expected: %0dx%0d, %0dbpp, text=%b, graphics=%b",
                 exp_h_active, exp_v_active,
                 exp_bpp == BPP_1 ? 1 : exp_bpp == BPP_2 ? 2 : exp_bpp == BPP_4 ? 4 : 8,
                 exp_is_text, exp_is_graphics);
        $display("  Actual:   %0dx%0d, %0dbpp, text=%b, graphics=%b",
                 params.h_active, params.v_active,
                 params.bpp == BPP_1 ? 1 : params.bpp == BPP_2 ? 2 : params.bpp == BPP_4 ? 4 : 8,
                 params.is_text, params.is_graphics);

        report_test("Horizontal resolution", params.h_active == exp_h_active);
        report_test("Vertical resolution", params.v_active == exp_v_active);
        report_test("Bits per pixel", params.bpp == exp_bpp);
        report_test("Text mode flag", params.is_text == exp_is_text);
        report_test("Graphics mode flag", params.is_graphics == exp_is_graphics);

        // Validate timing parameters are reasonable
        report_test("H total > H active", params.h_total > params.h_active);
        report_test("V total > V active", params.v_total > params.v_active);
        report_test("H sync within bounds",
                    params.h_sync_start < params.h_total &&
                    params.h_sync_end <= params.h_total);
        report_test("V sync within bounds",
                    params.v_sync_start < params.v_total &&
                    params.v_sync_end <= params.v_total);
    end
endtask

// Main test sequence
initial begin
    $display("================================================================");
    $display("VGA Mode Definitions Testbench");
    $display("Testing all 15 standard PC video modes");
    $display("================================================================");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    // Test all text modes
    test_mode(MODE_00H, "40x25 Text, 16 colors",   11'd320, 11'd400, BPP_4, 1'b1, 1'b0);
    test_mode(MODE_01H, "40x25 Text, 16 colors",   11'd320, 11'd400, BPP_4, 1'b1, 1'b0);
    test_mode(MODE_02H, "80x25 Text, 16 colors",   11'd640, 11'd400, BPP_4, 1'b1, 1'b0);
    test_mode(MODE_03H, "80x25 Text, 16 colors",   11'd640, 11'd400, BPP_4, 1'b1, 1'b0);
    test_mode(MODE_07H, "80x25 MDA Monochrome",    11'd720, 11'd350, BPP_1, 1'b1, 1'b0);

    // Test CGA graphics modes
    test_mode(MODE_04H, "320x200, 4 colors (CGA)", 11'd320, 11'd200, BPP_2, 1'b0, 1'b1);
    test_mode(MODE_05H, "320x200, 4 gray (CGA)",   11'd320, 11'd200, BPP_2, 1'b0, 1'b1);
    test_mode(MODE_06H, "640x200, 2 colors (CGA)", 11'd640, 11'd200, BPP_1, 1'b0, 1'b1);

    // Test EGA graphics modes
    test_mode(MODE_0DH, "320x200, 16 colors (EGA)", 11'd320, 11'd200, BPP_4, 1'b0, 1'b1);
    test_mode(MODE_0EH, "640x200, 16 colors (EGA)", 11'd640, 11'd200, BPP_4, 1'b0, 1'b1);
    test_mode(MODE_0FH, "640x350, Mono (EGA)",      11'd640, 11'd350, BPP_1, 1'b0, 1'b1);
    test_mode(MODE_10H, "640x350, 16 colors (EGA)", 11'd640, 11'd350, BPP_4, 1'b0, 1'b1);

    // Test VGA graphics modes
    test_mode(MODE_11H, "640x480, 2 colors (VGA)",  11'd640, 11'd480, BPP_1, 1'b0, 1'b1);
    test_mode(MODE_12H, "640x480, 16 colors (VGA)", 11'd640, 11'd480, BPP_4, 1'b0, 1'b1);
    test_mode(MODE_13H, "320x200, 256 colors (VGA)",11'd320, 11'd200, BPP_8, 1'b0, 1'b1);

    // Test text column/row parameters
    $display("");
    $display("Testing text mode parameters:");
    begin
        VideoModeParams_t params;

        params = get_mode_params(MODE_00H);
        $display("  Mode 00h: %0d columns x %0d rows", params.text_cols, params.text_rows);
        report_test("Mode 00h: 40 columns", params.text_cols == 7'd40);
        report_test("Mode 00h: 25 rows", params.text_rows == 6'd25);

        params = get_mode_params(MODE_03H);
        $display("  Mode 03h: %0d columns x %0d rows", params.text_cols, params.text_rows);
        report_test("Mode 03h: 80 columns", params.text_cols == 7'd80);
        report_test("Mode 03h: 25 rows", params.text_rows == 6'd25);

        params = get_mode_params(MODE_07H);
        $display("  Mode 07h: %0d columns x %0d rows", params.text_cols, params.text_rows);
        report_test("Mode 07h: 80 columns", params.text_cols == 7'd80);
        report_test("Mode 07h: 25 rows", params.text_rows == 6'd25);
    end

    // Test resolution categories
    $display("");
    $display("Testing resolution categories:");
    begin
        integer count_320x200, count_640x200, count_640x350, count_640x480, count_640x400, count_720x350;
        VideoModeParams_t params;

        count_320x200 = 0;
        count_640x200 = 0;
        count_640x350 = 0;
        count_640x480 = 0;
        count_640x400 = 0;
        count_720x350 = 0;

        // Count modes by resolution
        for (int m = 0; m <= 8'h13; m++) begin
            params = get_mode_params(VideoModeNumber_t'(m));
            if (params.h_active == 320 && params.v_active == 200) count_320x200++;
            if (params.h_active == 640 && params.v_active == 200) count_640x200++;
            if (params.h_active == 640 && params.v_active == 350) count_640x350++;
            if (params.h_active == 640 && params.v_active == 480) count_640x480++;
            if (params.h_active == 640 && params.v_active == 400) count_640x400++;
            if (params.h_active == 720 && params.v_active == 350) count_720x350++;
        end

        $display("  320x200 modes: %0d", count_320x200);
        $display("  640x200 modes: %0d", count_640x200);
        $display("  640x350 modes: %0d", count_640x350);
        $display("  640x400 modes: %0d", count_640x400);
        $display("  640x480 modes: %0d", count_640x480);
        $display("  720x350 modes: %0d (MDA)", count_720x350);

        report_test("Multiple 320x200 modes", count_320x200 >= 4);
        report_test("Multiple 640x200 modes", count_640x200 >= 2);
        report_test("Multiple 640x350 modes", count_640x350 >= 2);
        report_test("Multiple 640x480 modes", count_640x480 >= 2);
        report_test("MDA 720x350 mode exists", count_720x350 == 1);
    end

    // Test color depth categories
    $display("");
    $display("Testing color depth categories:");
    begin
        integer count_1bpp, count_2bpp, count_4bpp, count_8bpp;
        VideoModeParams_t params;

        count_1bpp = 0;
        count_2bpp = 0;
        count_4bpp = 0;
        count_8bpp = 0;

        for (int m = 0; m <= 8'h13; m++) begin
            params = get_mode_params(VideoModeNumber_t'(m));
            if (params.bpp == BPP_1) count_1bpp++;
            if (params.bpp == BPP_2) count_2bpp++;
            if (params.bpp == BPP_4) count_4bpp++;
            if (params.bpp == BPP_8) count_8bpp++;
        end

        $display("  1bpp (2 colors) modes: %0d", count_1bpp);
        $display("  2bpp (4 colors) modes: %0d", count_2bpp);
        $display("  4bpp (16 colors) modes: %0d", count_4bpp);
        $display("  8bpp (256 colors) modes: %0d", count_8bpp);

        report_test("1bpp modes exist", count_1bpp >= 3);  // 06h, 0Fh, 11h
        report_test("2bpp modes exist", count_2bpp >= 2);  // 04h, 05h
        report_test("4bpp modes exist", count_4bpp >= 6);  // Text + 0Dh, 0Eh, 10h, 12h
        report_test("8bpp mode exists", count_8bpp >= 1);  // 13h
    end

    // Print summary
    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0d%%", (pass_count * 100) / test_count);
    $display("================================================================");
    $display("");

    if (fail_count == 0) begin
        $display("*** ALL MODE DEFINITION TESTS PASSED ***");
        $display("");
        $display("Mode definitions complete for:");
        $display("  - 5 text modes (40-col, 80-col, MDA)");
        $display("  - 3 CGA graphics modes");
        $display("  - 4 EGA graphics modes");
        $display("  - 3 VGA graphics modes");
        $display("  TOTAL: 15 video modes");
    end else begin
        $display("*** SOME TESTS FAILED ***");
    end

    $display("");
    $display("Next steps:");
    $display("  1. Implement VGASync configurability");
    $display("  2. Update FrameBuffer for multi-resolution support");
    $display("  3. Add mode detection in VGARegisters");
    $display("  4. Create hardware integration tests");
    $display("================================================================");

    $finish;
end

// Timeout watchdog
initial begin
    #100000;  // 100us timeout
    $display("ERROR: Test timeout!");
    $finish;
end

endmodule
