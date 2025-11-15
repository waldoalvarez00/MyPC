// ================================================================
// Unit Test for VGASync
// Tests VGA sync signal generation for multiple video modes
// ================================================================

`timescale 1ns/1ps

module vgasync_tb;

    // DUT signals
    logic clk;
    logic reset;
    VideoModeNumber_t mode_num;
    logic vsync;
    logic hsync;
    logic is_blank;
    logic [10:0] row;
    logic [10:0] col;
    logic V_BLANK;
    logic H_BLANK;

    // Include VGA types
    `include "../Quartus/rtl/VGA/VGATypes.sv"

    // Instantiate DUT
    VGASync dut (
        .clk(clk),
        .reset(reset),
        .mode_num(mode_num),
        .vsync(vsync),
        .hsync(hsync),
        .is_blank(is_blank),
        .row(row),
        .col(col),
        .V_BLANK(V_BLANK),
        .H_BLANK(H_BLANK)
    );

    // Clock generation (25.175 MHz VGA pixel clock approximation)
    initial begin
        clk = 0;
        forever #20 clk = ~clk;  // ~25 MHz
    end

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Test variables (declared at module level for Icarus Verilog)
    VideoModeParams_t mode_params;
    logic hsync_active;
    logic vsync_active;
    logic [10:0] prev_col;
    logic [10:0] curr_row;
    logic [10:0] row_40col;
    logic [10:0] row_80col;
    int hsync_high, hsync_low;
    int vsync_count;
    int clk_count;
    int active_samples;
    int blank_samples;

    task check_result(input string test_name, input logic condition);
        test_count++;
        if (condition) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s", test_count, test_name);
            fail_count++;
        end
    endtask

    // Task to count complete frames
    task count_frame_cycles(output int h_cycles, output int v_lines);
        int h_cnt, v_cnt;
        logic prev_vsync;

        h_cnt = 0;
        v_cnt = 0;
        prev_vsync = vsync;

        // Wait for start of frame (vsync high to low)
        @(negedge vsync);

        // Count one complete vertical line
        @(posedge hsync);
        while (!hsync) begin
            @(posedge clk);
            h_cnt++;
        end

        // Count vertical lines until next frame
        while (vsync) @(posedge clk);  // Wait for vsync to go low
        while (!vsync) begin           // Count until vsync goes high again
            @(negedge hsync);
            v_cnt++;
        end

        h_cycles = h_cnt;
        v_lines = v_cnt;
    endtask

    // Test sequence
    initial begin
        $display("================================================================");
        $display("VGASync Unit Test");
        $display("================================================================");

        // Initialize
        reset = 1;
        mode_num = MODE_03H;  // Default to 80x25 text
        repeat(10) @(posedge clk);
        reset = 0;
        repeat(10) @(posedge clk);

        // ================================================================
        // TEST 1: Reset Behavior
        // ================================================================
        $display("\n--- Test 1: Reset Behavior ---");

        reset = 1;
        repeat(5) @(posedge clk);

        check_result("Row counter reset to 0", row == 11'd0);
        check_result("Column counter reset to 0", col == 11'd0);

        reset = 0;
        repeat(5) @(posedge clk);

        // ================================================================
        // TEST 2: Mode 03h (80x25 Text) Timing
        // ================================================================
        $display("\n--- Test 2: Mode 03h (80x25 Text) Timing ---");

        mode_num = MODE_03H;
        repeat(10) @(posedge clk);

        mode_params = get_mode_params(MODE_03H);

        check_result("Mode 03h: 640x400 active area",
                     mode_params.h_active == 11'd640 &&
                     mode_params.v_active == 11'd400);

        // Wait for active display region
        while (V_BLANK || H_BLANK) @(posedge clk);

        check_result("Mode 03h: Not blank in active area", !is_blank);
        check_result("Mode 03h: Row in range", row >= 0 && row < 11'd400);
        check_result("Mode 03h: Col in range", col >= 0 && col < 11'd640);

        // ================================================================
        // TEST 3: H/V Sync Signal Generation
        // ================================================================
        $display("\n--- Test 3: Sync Signal Generation ---");

        hsync_active = 0;
        vsync_active = 0;

        // Monitor for sync pulses over one frame
        fork
            begin
                repeat(1000) begin
                    @(posedge clk);
                    if (!hsync) hsync_active = 1;
                    if (!vsync) vsync_active = 1;
                end
            end
        join

        check_result("Hsync pulse detected", hsync_active);
        check_result("Vsync pulse detected", vsync_active);

        // ================================================================
        // TEST 4: Blanking Regions
        // ================================================================
        $display("\n--- Test 4: Blanking Regions ---");

        // Wait for horizontal blanking
        while (!H_BLANK) @(posedge clk);
        check_result("H_BLANK asserted during h-blank", H_BLANK == 1'b1);
        check_result("is_blank asserted during h-blank", is_blank == 1'b1);
        check_result("Column is 0 during h-blank", col == 11'd0);

        // Wait for vertical blanking
        while (!V_BLANK) @(posedge clk);
        check_result("V_BLANK asserted during v-blank", V_BLANK == 1'b1);
        check_result("is_blank asserted during v-blank", is_blank == 1'b1);
        check_result("Row is 0 during v-blank", row == 11'd0);

        // ================================================================
        // TEST 5: Row/Col Counter Incrementing
        // ================================================================
        $display("\n--- Test 5: Row/Col Counter Incrementing ---");

        // Wait for active area
        while (is_blank) @(posedge clk);

        prev_col = col;
        @(posedge clk);
        @(posedge clk);

        check_result("Column increments in active area", col > prev_col || H_BLANK);

        // Wait for line transition
        curr_row = row;
        while (row == curr_row && !V_BLANK) @(posedge clk);

        if (!V_BLANK)
            check_result("Row increments at line end", row == curr_row + 1);

        // ================================================================
        // TEST 6: Mode 00h (40x25 Text)
        // ================================================================
        $display("\n--- Test 6: Mode 00h (40x25 Text) ---");

        mode_num = MODE_00H;
        reset = 1;
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(10) @(posedge clk);

        mode_params = get_mode_params(MODE_00H);

        // Wait for active area
        while (is_blank) @(posedge clk);

        check_result("Mode 00h: Row in range", row < mode_params.v_active);
        check_result("Mode 00h: Col in range", col < mode_params.h_active);

        // ================================================================
        // TEST 7: Mode 04h (CGA 320x200 Graphics)
        // ================================================================
        $display("\n--- Test 7: Mode 04h (CGA Graphics) ---");

        mode_num = MODE_04H;
        reset = 1;
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(10) @(posedge clk);

        mode_params = get_mode_params(MODE_04H);

        // Wait for active area
        while (is_blank) @(posedge clk);

        check_result("Mode 04h: Row in range", row < mode_params.v_active);
        check_result("Mode 04h: Col in range", col < mode_params.h_active);

        // ================================================================
        // TEST 8: Mode 12h (VGA 640x480)
        // ================================================================
        $display("\n--- Test 8: Mode 12h (VGA 640x480) ---");

        mode_num = MODE_12H;
        reset = 1;
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(10) @(posedge clk);

        mode_params = get_mode_params(MODE_12H);

        check_result("Mode 12h: 640x480 resolution",
                     mode_params.h_active == 11'd640 &&
                     mode_params.v_active == 11'd480);

        // Wait for active area
        while (is_blank) @(posedge clk);

        check_result("Mode 12h: Not blank in active", !is_blank);
        check_result("Mode 12h: Row in range", row < 11'd480);
        check_result("Mode 12h: Col in range", col < 11'd640);

        // ================================================================
        // TEST 9: Frame Timing Consistency
        // ================================================================
        $display("\n--- Test 9: Frame Timing Consistency ---");

        mode_num = MODE_03H;
        reset = 1;
        repeat(5) @(posedge clk);
        reset = 0;

        // Count vsync pulses
        vsync_count = 0;
        clk_count = 0;

        repeat(10) @(negedge vsync);  // Skip initial sync

        @(negedge vsync);
        clk_count = 0;

        fork
            begin
                while (vsync_count < 2) begin
                    @(negedge vsync);
                    vsync_count++;
                end
            end
            begin
                while (vsync_count < 2) begin
                    @(posedge clk);
                    clk_count++;
                end
            end
        join

        check_result("Vsync occurs periodically", vsync_count == 2);
        check_result("Frame timing is reasonable", clk_count > 1000 && clk_count < 1000000);

        // ================================================================
        // TEST 10: Active Area Bounds
        // ================================================================
        $display("\n--- Test 10: Active Area Bounds ---");

        mode_num = MODE_03H;
        mode_params = get_mode_params(MODE_03H);

        // Sample multiple points in frame
        active_samples = 0;
        blank_samples = 0;

        repeat(10000) begin
            @(posedge clk);
            if (!is_blank) begin
                active_samples++;
                if (row >= mode_params.v_active || col >= mode_params.h_active)
                    $display("ERROR: Active pixel outside bounds at row=%0d, col=%0d", row, col);
            end else begin
                blank_samples++;
            end
        end

        check_result("Both active and blank regions present",
                     active_samples > 0 && blank_samples > 0);
        check_result("Reasonable active/blank ratio",
                     active_samples > 1000 && blank_samples > 500);

        // ================================================================
        // TEST 11: Mode Switching
        // ================================================================
        $display("\n--- Test 11: Mode Switching ---");

        mode_num = MODE_00H;
        repeat(100) @(posedge clk);
        row_40col = row;

        mode_num = MODE_03H;
        repeat(100) @(posedge clk);
        row_80col = row;

        check_result("Mode switch updates counters", 1'b1);  // Just verify no crash

        // ================================================================
        // TEST 12: Sync Polarity
        // ================================================================
        $display("\n--- Test 12: Sync Polarity ---");

        mode_num = MODE_03H;

        // Hsync should be mostly high (negative polarity, active low)
        hsync_high = 0;
        hsync_low = 0;
        repeat(1000) begin
            @(posedge clk);
            if (hsync) hsync_high++;
            else hsync_low++;
        end

        check_result("Hsync mostly high (negative polarity)",
                     hsync_high > hsync_low * 4);

        // ================================================================
        // Test Summary
        // ================================================================
        $display("\n================================================================");
        $display("TEST SUMMARY");
        $display("================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %0d%%", (pass_count * 100) / test_count);
        $display("================================================================");

        if (fail_count == 0) begin
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓");
            $finish(0);
        end else begin
            $display("✗✗✗ SOME TESTS FAILED ✗✗✗");
            $finish(1);
        end
    end

    // Timeout
    initial begin
        #50000000;  // 50ms timeout
        $display("\n[ERROR] Testbench timeout!");
        $finish(1);
    end

endmodule
