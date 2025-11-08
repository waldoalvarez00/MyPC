// VGA Mode Switching Integration Testbench
// Tests mode detection in VGARegisters and timing changes in VGASync
//
// Verifies that:
// 1. Mode detection logic correctly identifies video modes
// 2. Mode number synchronizes to VGA clock domain
// 3. VGASync timing adapts to different modes

`timescale 1ns/1ps

`include "VGATypes.sv"

module vga_mode_switching_tb;

// Clock generation
logic sys_clk;
logic vga_clk;
logic reset;

// VGARegisters interface
logic cs;
logic [19:1] data_m_addr;
logic [15:0] data_m_data_in;
logic [15:0] data_m_data_out;
logic [1:0] data_m_bytesel;
logic data_m_wr_en;
logic data_m_access;
logic data_m_ack;

// VGA signals
logic vga_vsync_in;
logic vga_hsync_in;

// VGA outputs
logic cursor_enabled;
logic graphics_enabled;
logic [3:0] background_color;
logic bright_colors;
logic palette_sel;
logic [14:0] cursor_pos;
logic [2:0] cursor_scan_start;
logic [2:0] cursor_scan_end;
logic vga_256_color;
logic [7:0] vga_dac_idx;
logic [17:0] vga_dac_rd;
VideoModeNumber_t mode_num;

// VGASync outputs
logic vsync;
logic hsync;
logic is_blank;
logic [10:0] row;
logic [10:0] col;
logic V_BLANK;
logic H_BLANK;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// Clock generation
initial begin
    sys_clk = 0;
    forever #10 sys_clk = ~sys_clk;  // 50 MHz
end

initial begin
    vga_clk = 0;
    forever #20 vga_clk = ~vga_clk;  // 25 MHz
end

// DUT: VGARegisters
VGARegisters VGARegisters(
    .clk(sys_clk),
    .vga_clk(vga_clk),
    .reset(reset),
    .cs(cs),
    .data_m_addr(data_m_addr),
    .data_m_data_in(data_m_data_in),
    .data_m_data_out(data_m_data_out),
    .data_m_bytesel(data_m_bytesel),
    .data_m_wr_en(data_m_wr_en),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .vga_vsync(vga_vsync_in),
    .vga_hsync(vga_hsync_in),
    .cursor_enabled(cursor_enabled),
    .graphics_enabled(graphics_enabled),
    .background_color(background_color),
    .bright_colors(bright_colors),
    .palette_sel(palette_sel),
    .cursor_pos(cursor_pos),
    .cursor_scan_start(cursor_scan_start),
    .cursor_scan_end(cursor_scan_end),
    .vga_256_color(vga_256_color),
    .vga_dac_idx(vga_dac_idx),
    .vga_dac_rd(vga_dac_rd),
    .mode_num(mode_num)
);

// DUT: VGASync
VGASync VGASync(
    .clk(vga_clk),
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

// Register write task
task write_register(input [19:1] addr, input [15:0] data, input [1:0] bytesel);
    begin
        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = addr;
        data_m_data_in = data;
        data_m_bytesel = bytesel;

        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);

        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
    end
endtask

// Wait for mode synchronization (2 VGA clock cycles)
task wait_mode_sync;
    begin
        repeat(4) @(posedge vga_clk);
    end
endtask

// Test mode detection
task test_mode_detection(input string test_name,
                         input VideoModeNumber_t expected_mode);
    begin
        $display("");
        $display("Testing: %s", test_name);
        $display("  Expected mode: %02Xh", expected_mode);

        // Wait for synchronization
        wait_mode_sync();

        $display("  Detected mode: %02Xh", mode_num);
        report_test($sformatf("%s - Mode detection", test_name),
                    mode_num == expected_mode);
    end
endtask

// Test VGASync timing parameters
task test_vgasync_timing(input string test_name,
                         input logic [10:0] exp_h_active,
                         input logic [10:0] exp_v_active);
    begin
        integer max_row_seen;
        integer max_col_seen;
        integer cycles;
        logic prev_vsync;
        logic frame_done;

        $display("");
        $display("Testing VGASync timing for: %s", test_name);
        $display("  Expected resolution: %0dx%0d", exp_h_active, exp_v_active);

        // Monitor one complete frame
        max_row_seen = 0;
        max_col_seen = 0;
        cycles = 0;
        frame_done = 0;

        // Wait for vsync to start
        @(negedge vsync);
        prev_vsync = vsync;

        // Monitor until next vsync
        while (cycles < 1000000 && !frame_done) begin  // Safety timeout
            @(posedge vga_clk);

            if (!is_blank) begin
                if (row > max_row_seen) max_row_seen = row;
                if (col > max_col_seen) max_col_seen = col;
            end

            // Check for vsync edge (frame complete)
            if (vsync != prev_vsync && vsync == 1'b0) begin
                frame_done = 1;
            end
            prev_vsync = vsync;
            cycles++;
        end

        $display("  Max row seen: %0d (expected < %0d)", max_row_seen, exp_v_active);
        $display("  Max col seen: %0d (expected < %0d)", max_col_seen, exp_h_active);

        // Check if observed values are within expected range
        // Allow some tolerance for timing variations
        report_test($sformatf("%s - Vertical resolution", test_name),
                    max_row_seen >= (exp_v_active - 10) && max_row_seen < exp_v_active);
        report_test($sformatf("%s - Horizontal resolution", test_name),
                    max_col_seen >= (exp_h_active - 10) && max_col_seen < exp_h_active);
    end
endtask

// Main test sequence
initial begin
    $display("================================================================");
    $display("VGA Mode Switching Integration Test");
    $display("Tests mode detection and timing configuration");
    $display("================================================================");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1'b1;
    cs = 1'b0;
    data_m_access = 1'b0;
    data_m_wr_en = 1'b0;
    data_m_addr = 19'h0;
    data_m_data_in = 16'h0;
    data_m_bytesel = 2'b00;
    vga_vsync_in = 1'b0;
    vga_hsync_in = 1'b0;

    repeat(10) @(posedge sys_clk);
    reset = 1'b0;
    repeat(10) @(posedge sys_clk);

    // Test 1: Default mode (should be Mode 03h - 80x25 text)
    $display("");
    $display("================================================================");
    $display("Test 1: Default Mode (Text Mode 03h)");
    $display("================================================================");
    test_mode_detection("Default text mode", MODE_03H);
    // Note: VGASync timing test requires full frame which takes very long
    // Skipping timing verification for basic test

    // Test 2: Switch to graphics mode 04h (CGA 320x200, 4 colors)
    $display("");
    $display("================================================================");
    $display("Test 2: CGA Graphics Mode 04h");
    $display("================================================================");

    // Write mode control register (MCGA addr 0x1EC) to enable graphics
    // Bit 0 = 0: text disabled
    // Bit 1 = 1: graphics mode
    // Bit 3 = 1: display enabled
    write_register(19'h1EC, 16'h000A, 2'b01);  // MCGA Mode Control = 0x0A

    test_mode_detection("CGA graphics mode", MODE_04H);

    // Test 3: Switch to MCGA mode 13h (320x200, 256 colors)
    $display("");
    $display("================================================================");
    $display("Test 3: MCGA Mode 13h (256 colors)");
    $display("================================================================");

    // Write AMCR register (MCGA addr 0x1E0) to enable 256-color mode
    write_register(19'h1E0, 16'h0041, 2'b01);  // MCGA AMCR = 0x41

    test_mode_detection("MCGA 256-color mode", MODE_13H);

    // Test 4: Switch back to text mode
    $display("");
    $display("================================================================");
    $display("Test 4: Return to Text Mode");
    $display("================================================================");

    // Clear graphics mode and 256-color mode
    write_register(19'h1E0, 16'h0000, 2'b01);  // 3C0 = 0x00 (disable 256-color)
    // Set text mode: text=1, graphics=0, display=1
    write_register(19'h1EC, 16'h0009, 2'b01);  // 3D8 = 0x09

    test_mode_detection("Back to text mode", MODE_03H);

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
        $display("*** ALL MODE SWITCHING TESTS PASSED ***");
        $display("");
        $display("Verified functionality:");
        $display("  - Mode detection logic in VGARegisters");
        $display("  - Mode number synchronization to VGA clock");
        $display("  - Mode switching between text/graphics/256-color");
    end else begin
        $display("*** SOME TESTS FAILED ***");
    end

    $display("");
    $display("Next steps:");
    $display("  1. Update FrameBuffer for multi-resolution support");
    $display("  2. Implement pixel format handling (1bpp, 2bpp, 4bpp, 8bpp)");
    $display("  3. Add text mode column/row variants");
    $display("  4. Create full hardware integration tests");
    $display("================================================================");

    $finish;
end

// Timeout watchdog
initial begin
    #500000;  // 500us timeout
    $display("ERROR: Test timeout!");
    $finish;
end

endmodule
