// VGA Complete Modes Test - All 15 video modes
// Tests all standard PC video modes including CGA, EGA, VGA, and MDA

`timescale 1ns/1ps

`include "VGATypes.sv"

module vga_complete_modes_tb;

// Clocks
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

// Outputs
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

// Test tracking
integer tests_run = 0;
integer tests_passed = 0;
integer tests_failed = 0;

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
    .vga_vsync(1'b0),
    .vga_hsync(1'b0),
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

// Task to write to CRTC indexed registers
task write_crtc_register(input [5:0] crtc_index, input [7:0] crtc_value);
    begin
        // Write index
        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = 19'h1EA;  // CRTC Index Register
        data_m_data_in = {8'h00, 2'b00, crtc_index};
        data_m_bytesel = 2'b01;
        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);
        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;

        // Write value
        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = 19'h1EA;  // CRTC Data Register
        data_m_data_in = {crtc_value, 8'h00};
        data_m_bytesel = 2'b10;
        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);
        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
    end
endtask

// Task to write Mode Control Register
task write_mode_register(input [7:0] mode_value);
    begin
        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = 19'h1EC;
        data_m_data_in = {8'h00, mode_value};
        data_m_bytesel = 2'b01;
        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);
        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
    end
endtask

// Task to write AMCR register
task write_amcr_register(input [7:0] amcr_value);
    begin
        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = 19'h1E0;
        data_m_data_in = {8'h00, amcr_value};
        data_m_bytesel = 2'b01;
        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);
        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
    end
endtask

// Task to set up a video mode
task setup_mode(
    input [7:0] horiz_display_end,
    input [9:0] vert_display_end,
    input [4:0] max_scan_line,
    input [7:0] mode_control,
    input [7:0] amcr_value
);
    begin
        // Set CRTC registers
        write_crtc_register(6'h01, horiz_display_end);                    // Horizontal Display End
        write_crtc_register(6'h12, vert_display_end[7:0]);                // Vertical Display End (low)
        write_crtc_register(6'h07, {1'b0, vert_display_end[9], 5'b0, vert_display_end[8], 1'b0}); // Overflow
        write_crtc_register(6'h09, {3'b0, max_scan_line});                // Maximum Scan Line

        // Set mode control register
        write_mode_register(mode_control);

        // Set AMCR if needed
        if (amcr_value != 8'h00)
            write_amcr_register(amcr_value);

        // Wait for clock domain crossing
        repeat(15) @(posedge vga_clk);
    end
endtask

// Test a specific mode
task test_mode(
    input [7:0] horiz_display_end,
    input [9:0] vert_display_end,
    input [4:0] max_scan_line,
    input [7:0] mode_control,
    input [7:0] amcr_value,
    input [7:0] expected_mode,
    input string mode_name
);
    begin
        $display("");
        $display("================================================================");
        $display("Test: %s", mode_name);
        $display("================================================================");
        $display("  CRTC Settings:");
        $display("    Horiz Display End: %0d (0x%02h)", horiz_display_end, horiz_display_end);
        $display("    Vert Display End:  %0d (0x%03h)", vert_display_end, vert_display_end);
        $display("    Max Scan Line:     %0d", max_scan_line);
        $display("  Mode Control: 0x%02h", mode_control);
        if (amcr_value != 8'h00)
            $display("  AMCR: 0x%02h", amcr_value);

        setup_mode(horiz_display_end, vert_display_end, max_scan_line, mode_control, amcr_value);

        $display("  Expected mode: %02hh", expected_mode);
        $display("  Detected mode: %02hh", mode_num);

        tests_run = tests_run + 1;
        if (mode_num == expected_mode) begin
            $display("  [PASS] %s", mode_name);
            tests_passed = tests_passed + 1;
        end else begin
            $display("  [FAIL] %s - Got %02hh, expected %02hh", mode_name, mode_num, expected_mode);
            tests_failed = tests_failed + 1;
        end
    end
endtask

// Main test sequence
initial begin
    $display("================================================================");
    $display("VGA Complete Modes Test - All 15 Video Modes");
    $display("================================================================");

    // Initialize
    reset = 1'b1;
    cs = 1'b0;
    data_m_access = 1'b0;
    data_m_wr_en = 1'b0;
    data_m_addr = 19'h0;
    data_m_data_in = 16'h0;
    data_m_bytesel = 2'b00;

    repeat(10) @(posedge sys_clk);
    reset = 1'b0;
    repeat(10) @(posedge sys_clk);

    $display("");
    $display("Testing CGA Text Modes (00h-03h)");
    $display("================================================================");

    // Mode 00h: 40x25 text, B&W
    test_mode(8'd39, 10'd199, 5'd7, 8'h04, 8'h00, MODE_00H, "Mode 00h: 40x25 text B&W");

    // Mode 01h: 40x25 text, color
    test_mode(8'd39, 10'd199, 5'd7, 8'h00, 8'h00, MODE_01H, "Mode 01h: 40x25 text color");

    // Mode 02h: 80x25 text, B&W
    test_mode(8'd79, 10'd199, 5'd7, 8'h05, 8'h00, MODE_02H, "Mode 02h: 80x25 text B&W");

    // Mode 03h: 80x25 text, color
    test_mode(8'd79, 10'd199, 5'd7, 8'h09, 8'h00, MODE_03H, "Mode 03h: 80x25 text color");

    $display("");
    $display("Testing CGA Graphics Modes (04h-06h)");
    $display("================================================================");

    // Mode 04h: 320x200, 4 colors
    test_mode(8'd39, 10'd199, 5'd1, 8'h0A, 8'h00, MODE_04H, "Mode 04h: 320x200 4-color");

    // Mode 05h: 320x200, 4 grays
    test_mode(8'd39, 10'd199, 5'd1, 8'h0E, 8'h00, MODE_05H, "Mode 05h: 320x200 4-gray");

    // Mode 06h: 640x200, 2 colors (use bw_mode=1 to distinguish from mode 0Eh)
    test_mode(8'd79, 10'd199, 5'd1, 8'h1E, 8'h00, MODE_06H, "Mode 06h: 640x200 2-color");

    $display("");
    $display("Testing MDA Text Mode (07h)");
    $display("================================================================");

    // Mode 07h: 80x25 MDA text, monochrome (720x350)
    test_mode(8'd89, 10'd349, 5'd13, 8'h09, 8'h00, MODE_07H, "Mode 07h: 80x25 MDA monochrome");

    $display("");
    $display("Testing EGA Graphics Modes (0Dh-10h)");
    $display("================================================================");

    // Mode 0Dh: 320x200, 16 colors (EGA - requires 80-column mode, bit0=1, bit1=1, bit4=0)
    test_mode(8'd79, 10'd199, 5'd1, 8'h0B, 8'h00, MODE_0DH, "Mode 0Dh: 320x200 16-color (EGA)");

    // Mode 0Eh: 640x200, 16 colors (use bw_mode=0 to distinguish from mode 06h)
    test_mode(8'd79, 10'd199, 5'd1, 8'h1A, 8'h00, MODE_0EH, "Mode 0Eh: 640x200 16-color (EGA)");

    // Mode 0Fh: 640x350, monochrome
    test_mode(8'd79, 10'd349, 5'd13, 8'h1E, 8'h00, MODE_0FH, "Mode 0Fh: 640x350 monochrome (EGA)");

    // Mode 10h: 640x350, 16 colors
    test_mode(8'd79, 10'd349, 5'd13, 8'h1A, 8'h00, MODE_10H, "Mode 10h: 640x350 16-color (EGA)");

    $display("");
    $display("Testing VGA Graphics Modes (11h-13h)");
    $display("================================================================");

    // Mode 11h: 640x480, 2 colors
    test_mode(8'd79, 10'd479, 5'd15, 8'h1E, 8'h00, MODE_11H, "Mode 11h: 640x480 2-color (VGA)");

    // Mode 12h: 640x480, 16 colors
    test_mode(8'd79, 10'd479, 5'd15, 8'h1A, 8'h00, MODE_12H, "Mode 12h: 640x480 16-color (VGA)");

    // Mode 13h: 320x200, 256 colors (MCGA/VGA)
    test_mode(8'd79, 10'd199, 5'd1, 8'h0A, 8'h41, MODE_13H, "Mode 13h: 320x200 256-color (MCGA)");

    // Print summary
    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", tests_run);
    $display("Passed:      %0d", tests_passed);
    $display("Failed:      %0d", tests_failed);
    $display("Success Rate: %0d%%", (tests_passed * 100) / tests_run);
    $display("================================================================");

    if (tests_failed == 0) begin
        $display("");
        $display("*** ALL 15 VIDEO MODE TESTS PASSED ***");
        $display("");
        $display("Verified modes:");
        $display("  - CGA Text:     00h-03h (40/80 col, B&W/color)");
        $display("  - CGA Graphics: 04h-06h (320x200, 640x200)");
        $display("  - MDA Text:     07h (80x25 monochrome)");
        $display("  - EGA Graphics: 0Dh-10h (320x200, 640x200, 640x350)");
        $display("  - VGA Graphics: 11h-12h (640x480)");
        $display("  - MCGA:         13h (320x200 256-color)");
        $display("");
        $display("Complete coverage: 15/15 modes (100%)");
    end else begin
        $display("");
        $display("*** SOME TESTS FAILED ***");
    end

    $display("================================================================");
    $finish;
end

// Timeout
initial begin
    #200000;
    $display("ERROR: Test timeout!");
    $finish;
end

endmodule
