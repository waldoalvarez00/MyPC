// VGA All Modes Test - Comprehensive mode detection test
// Tests all 8 currently detectable video modes

`timescale 1ns/1ps

`include "VGATypes.sv"

module vga_all_modes_tb;

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

// Register write task
task write_mode_register(input [7:0] mode_value);
    begin
        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = 19'h1EC;  // Mode Control Register
        data_m_data_in = {8'h00, mode_value};
        data_m_bytesel = 2'b01;  // Lower byte

        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);

        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
    end
endtask

// Write AMCR register (for mode 13h)
task write_amcr_register(input [7:0] amcr_value);
    begin
        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = 19'h1E0;  // AMCR Register
        data_m_data_in = {8'h00, amcr_value};
        data_m_bytesel = 2'b01;  // Lower byte

        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);

        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
    end
endtask

// Test a specific mode
task test_mode(input [7:0] mode_value, input [7:0] expected_mode, input string mode_name);
    begin
        $display("");
        $display("================================================================");
        $display("Test: %s", mode_name);
        $display("================================================================");
        $display("  Writing 0x%02h to Mode Control Register", mode_value);

        write_mode_register(mode_value);

        // Wait for clock domain crossing
        repeat(10) @(posedge vga_clk);

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

// Test mode 13h (requires AMCR)
task test_mode_13h();
    begin
        $display("");
        $display("================================================================");
        $display("Test: Mode 13h (320x200, 256 colors)");
        $display("================================================================");
        $display("  Writing 0x41 to AMCR Register");

        write_amcr_register(8'h41);

        // Wait for clock domain crossing
        repeat(10) @(posedge vga_clk);

        $display("  Expected mode: 13h");
        $display("  Detected mode: %02hh", mode_num);

        tests_run = tests_run + 1;
        if (mode_num == MODE_13H) begin
            $display("  [PASS] Mode 13h");
            tests_passed = tests_passed + 1;
        end else begin
            $display("  [FAIL] Mode 13h - Got %02hh, expected 13h", mode_num);
            tests_failed = tests_failed + 1;
        end
    end
endtask

// Main test sequence
initial begin
    $display("================================================================");
    $display("VGA All Modes Detection Test");
    $display("Testing all 8 detectable video modes (CGA + MCGA)");
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

    // Test all CGA text modes
    // Mode 00h: 40x25 text, B&W
    // Bit pattern: hres=0, graphics_320=0, bw=1
    // Mode register = 0b00000100 = 0x04
    test_mode(8'h04, MODE_00H, "Mode 00h (40x25 text B&W)");

    // Mode 01h: 40x25 text, 16 colors
    // Bit pattern: hres=0, graphics_320=0, bw=0
    // Mode register = 0b00000000 = 0x00
    test_mode(8'h00, MODE_01H, "Mode 01h (40x25 text color)");

    // Mode 02h: 80x25 text, B&W
    // Bit pattern: hres=1, graphics_320=0, bw=1
    // Mode register = 0b00000101 = 0x05
    test_mode(8'h05, MODE_02H, "Mode 02h (80x25 text B&W)");

    // Mode 03h: 80x25 text, 16 colors (most common)
    // Bit pattern: hres=1, graphics_320=0, bw=0, video_enabled=1
    // Mode register = 0b00001001 = 0x09
    test_mode(8'h09, MODE_03H, "Mode 03h (80x25 text color)");

    // Test all CGA graphics modes
    // Mode 04h: 320x200, 4 colors
    // Bit pattern: graphics_320=1, bw=0, video_enabled=1
    // Mode register = 0b00001010 = 0x0A
    test_mode(8'h0A, MODE_04H, "Mode 04h (320x200 4-color)");

    // Mode 05h: 320x200, 4 grays
    // Bit pattern: graphics_320=1, bw=1, video_enabled=1
    // Mode register = 0b00001110 = 0x0E
    test_mode(8'h0E, MODE_05H, "Mode 05h (320x200 4-gray)");

    // Mode 06h: 640x200, 2 colors
    // Bit pattern: mode_640=1, video_enabled=1
    // Mode register = 0b00011010 = 0x1A
    test_mode(8'h1A, MODE_06H, "Mode 06h (640x200 2-color)");

    // Mode 13h: 320x200, 256 colors (MCGA/VGA)
    // Requires AMCR = 0x41
    // First reset AMCR, then set mode
    write_amcr_register(8'h00);
    repeat(5) @(posedge sys_clk);
    test_mode_13h();

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
        $display("*** ALL MODE DETECTION TESTS PASSED ***");
        $display("");
        $display("Verified modes:");
        $display("  - CGA Text: 00h, 01h, 02h, 03h (40/80 col, B&W/color)");
        $display("  - CGA Graphics: 04h, 05h, 06h (320x200, 640x200)");
        $display("  - MCGA: 13h (320x200, 256 colors)");
        $display("");
        $display("Total: 8 modes fully functional");
    end else begin
        $display("");
        $display("*** SOME TESTS FAILED ***");
    end

    $display("================================================================");
    $finish;
end

// Timeout
initial begin
    #100000;
    $display("ERROR: Test timeout!");
    $finish;
end

endmodule
