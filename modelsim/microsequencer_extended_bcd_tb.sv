//============================================================================
//
//  MicroSequencer Extended BCD Testbench
//  Tests microcode execution engine for FPU complex operations
//
//  Copyright Waldo Alvarez, 2025
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module microsequencer_extended_bcd_tb;

//============================================================================
// Clock and Reset
//============================================================================

reg clk;
reg reset;

initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 50 MHz clock
end

//============================================================================
// DUT Signals
//============================================================================

// Control
reg        start;
reg [4:0]  micro_program_index;
wire       instruction_complete;

// Data bus
reg [79:0] data_in;
wire [79:0] data_out;

// Debug registers
wire [79:0] debug_temp_result;
wire [79:0] debug_temp_fp_a;
wire [79:0] debug_temp_fp_b;
wire [79:0] debug_temp_fp_c;
wire [63:0] debug_temp_uint64;
wire        debug_temp_sign;

// Arithmetic unit interface
wire [4:0]  arith_operation;
wire        arith_enable;
reg  [1:0]  arith_rounding_mode;
wire [79:0] arith_operand_a;
wire [79:0] arith_operand_b;
wire signed [15:0] arith_int16_in;
wire signed [31:0] arith_int32_in;
wire [63:0] arith_uint64_in;
wire        arith_uint64_sign_in;
wire [31:0] arith_fp32_in;
wire [63:0] arith_fp64_in;

// Arithmetic results
reg  [79:0] arith_result;
reg  [79:0] arith_result_secondary;
reg  signed [15:0] arith_int16_out;
reg  signed [31:0] arith_int32_out;
reg  [63:0] arith_uint64_out;
reg         arith_uint64_sign_out;
reg  [31:0] arith_fp32_out;
reg  [63:0] arith_fp64_out;
reg         arith_done;
reg         arith_invalid;
reg         arith_overflow;
reg         arith_cc_less;
reg         arith_cc_equal;
reg         arith_cc_greater;
reg         arith_cc_unordered;

// BCD to Binary interface
wire        bcd2bin_enable;
wire [79:0] bcd2bin_bcd_in;
reg  [63:0] bcd2bin_binary_out;
reg         bcd2bin_sign_out;
reg         bcd2bin_done;
reg         bcd2bin_error;

// Binary to BCD interface
wire        bin2bcd_enable;
wire [63:0] bin2bcd_binary_in;
wire        bin2bcd_sign_in;
reg  [79:0] bin2bcd_bcd_out;
reg         bin2bcd_done;
reg         bin2bcd_error;

// Payne-Hanek ROM interface
wire [2:0]  ph_rom_addr;
reg  [79:0] ph_rom_data;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
integer timeout_count;

//============================================================================
// Program Index Definitions
//============================================================================

localparam PROG_FADD     = 5'd0;
localparam PROG_FSUB     = 5'd1;
localparam PROG_FMUL     = 5'd2;
localparam PROG_FDIV     = 5'd3;
localparam PROG_FSQRT    = 5'd4;
localparam PROG_FSIN     = 5'd5;
localparam PROG_FCOS     = 5'd6;
localparam PROG_FLD      = 5'd7;
localparam PROG_FST      = 5'd8;
localparam PROG_FPREM    = 5'd9;
localparam PROG_FXTRACT  = 5'd10;
localparam PROG_FSCALE   = 5'd11;
localparam PROG_FBLD     = 5'd12;
localparam PROG_FBSTP    = 5'd13;
localparam PROG_FPTAN    = 5'd14;
localparam PROG_FPATAN   = 5'd15;
localparam PROG_F2XM1    = 5'd16;
localparam PROG_FYL2X    = 5'd17;
localparam PROG_FYL2XP1  = 5'd18;
localparam PROG_FSINCOS  = 5'd19;
localparam PROG_FPREM1   = 5'd20;
localparam PROG_FRNDINT  = 5'd21;

//============================================================================
// FP80 Constants
//============================================================================

localparam FP80_ZERO     = 80'h0000_0000000000000000;
localparam FP80_ONE      = 80'h3FFF_8000000000000000;
localparam FP80_TWO      = 80'h4000_8000000000000000;
localparam FP80_NEG_ONE  = 80'hBFFF_8000000000000000;

//============================================================================
// DUT Instantiation
//============================================================================

MicroSequencer_Extended_BCD dut (
    .clk(clk),
    .reset(reset),
    .start(start),
    .micro_program_index(micro_program_index),
    .instruction_complete(instruction_complete),
    .data_in(data_in),
    .data_out(data_out),
    .debug_temp_result(debug_temp_result),
    .debug_temp_fp_a(debug_temp_fp_a),
    .debug_temp_fp_b(debug_temp_fp_b),
    .debug_temp_fp_c(debug_temp_fp_c),
    .debug_temp_uint64(debug_temp_uint64),
    .debug_temp_sign(debug_temp_sign),
    .arith_operation(arith_operation),
    .arith_enable(arith_enable),
    .arith_rounding_mode(arith_rounding_mode),
    .arith_operand_a(arith_operand_a),
    .arith_operand_b(arith_operand_b),
    .arith_int16_in(arith_int16_in),
    .arith_int32_in(arith_int32_in),
    .arith_uint64_in(arith_uint64_in),
    .arith_uint64_sign_in(arith_uint64_sign_in),
    .arith_fp32_in(arith_fp32_in),
    .arith_fp64_in(arith_fp64_in),
    .arith_result(arith_result),
    .arith_result_secondary(arith_result_secondary),
    .arith_int16_out(arith_int16_out),
    .arith_int32_out(arith_int32_out),
    .arith_uint64_out(arith_uint64_out),
    .arith_uint64_sign_out(arith_uint64_sign_out),
    .arith_fp32_out(arith_fp32_out),
    .arith_fp64_out(arith_fp64_out),
    .arith_done(arith_done),
    .arith_invalid(arith_invalid),
    .arith_overflow(arith_overflow),
    .arith_cc_less(arith_cc_less),
    .arith_cc_equal(arith_cc_equal),
    .arith_cc_greater(arith_cc_greater),
    .arith_cc_unordered(arith_cc_unordered),
    .bcd2bin_enable(bcd2bin_enable),
    .bcd2bin_bcd_in(bcd2bin_bcd_in),
    .bcd2bin_binary_out(bcd2bin_binary_out),
    .bcd2bin_sign_out(bcd2bin_sign_out),
    .bcd2bin_done(bcd2bin_done),
    .bcd2bin_error(bcd2bin_error),
    .bin2bcd_enable(bin2bcd_enable),
    .bin2bcd_binary_in(bin2bcd_binary_in),
    .bin2bcd_sign_in(bin2bcd_sign_in),
    .bin2bcd_bcd_out(bin2bcd_bcd_out),
    .bin2bcd_done(bin2bcd_done),
    .bin2bcd_error(bin2bcd_error),
    .ph_rom_addr(ph_rom_addr),
    .ph_rom_data(ph_rom_data)
);

//============================================================================
// Stub Arithmetic Unit - Pulse-triggered protocol
// arith_enable is a one-cycle pulse, not a held signal
//============================================================================

reg [4:0] arith_delay;
reg arith_enable_prev;  // For edge detection

always @(posedge clk or posedge reset) begin
    if (reset) begin
        arith_done <= 1'b0;
        arith_result <= 80'd0;
        arith_result_secondary <= 80'd0;
        arith_invalid <= 1'b0;
        arith_overflow <= 1'b0;
        arith_cc_less <= 1'b0;
        arith_cc_equal <= 1'b0;
        arith_cc_greater <= 1'b0;
        arith_cc_unordered <= 1'b0;
        arith_delay <= 5'd0;
        arith_enable_prev <= 1'b0;
    end else begin
        arith_enable_prev <= arith_enable;

        // Detect rising edge of arith_enable (pulse)
        if (arith_enable && !arith_enable_prev) begin
            // New operation started - reset done and start countdown
            arith_done <= 1'b0;
            arith_delay <= 5'd8;  // 8-cycle delay
            $display("[STUB ARITH] Pulse detected, starting countdown for op=%d", arith_operation);
        end
        // Count down
        else if (arith_delay > 1) begin
            arith_delay <= arith_delay - 1;
        end
        // Complete operation
        else if (arith_delay == 1) begin
            arith_delay <= 5'd0;
            arith_done <= 1'b1;
            // Simple stub: return operand_a as result
            arith_result <= arith_operand_a;
            arith_result_secondary <= arith_operand_b;
            $display("[STUB ARITH] Done, result=%h", arith_operand_a);
        end
        // arith_done stays high until next operation starts
    end
end

//============================================================================
// Stub BCD Converters - Pulse-triggered protocol
//============================================================================

reg [3:0] bcd2bin_delay;
reg [3:0] bin2bcd_delay;
reg bcd2bin_enable_prev;
reg bin2bcd_enable_prev;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        bcd2bin_done <= 1'b0;
        bcd2bin_binary_out <= 64'd0;
        bcd2bin_sign_out <= 1'b0;
        bcd2bin_error <= 1'b0;
        bcd2bin_delay <= 4'd0;
        bcd2bin_enable_prev <= 1'b0;
    end else begin
        bcd2bin_enable_prev <= bcd2bin_enable;

        // Detect rising edge of bcd2bin_enable (pulse)
        if (bcd2bin_enable && !bcd2bin_enable_prev) begin
            bcd2bin_done <= 1'b0;
            bcd2bin_delay <= 4'd6;
            $display("[STUB BCD2BIN] Pulse detected, starting countdown");
        end
        // Count down
        else if (bcd2bin_delay > 1) begin
            bcd2bin_delay <= bcd2bin_delay - 1;
        end
        // Complete operation
        else if (bcd2bin_delay == 1) begin
            bcd2bin_delay <= 4'd0;
            bcd2bin_done <= 1'b1;
            bcd2bin_binary_out <= 64'd12345;  // Test value
            bcd2bin_sign_out <= 1'b0;
            $display("[STUB BCD2BIN] Done");
        end
        // done stays high until next operation
    end
end

always @(posedge clk or posedge reset) begin
    if (reset) begin
        bin2bcd_done <= 1'b0;
        bin2bcd_bcd_out <= 80'd0;
        bin2bcd_error <= 1'b0;
        bin2bcd_delay <= 4'd0;
        bin2bcd_enable_prev <= 1'b0;
    end else begin
        bin2bcd_enable_prev <= bin2bcd_enable;

        // Detect rising edge of bin2bcd_enable (pulse)
        if (bin2bcd_enable && !bin2bcd_enable_prev) begin
            bin2bcd_done <= 1'b0;
            bin2bcd_delay <= 4'd6;
            $display("[STUB BIN2BCD] Pulse detected, starting countdown");
        end
        // Count down
        else if (bin2bcd_delay > 1) begin
            bin2bcd_delay <= bin2bcd_delay - 1;
        end
        // Complete operation
        else if (bin2bcd_delay == 1) begin
            bin2bcd_delay <= 4'd0;
            bin2bcd_done <= 1'b1;
            bin2bcd_bcd_out <= 80'h12345;  // Test value
            $display("[STUB BIN2BCD] Done");
        end
        // done stays high until next operation
    end
end

//============================================================================
// Stub Payne-Hanek ROM
//============================================================================

always @(*) begin
    case (ph_rom_addr)
        3'd0: ph_rom_data = 80'h3FFF_8000000000000000;  // 1.0
        3'd1: ph_rom_data = 80'h4000_8000000000000000;  // 2.0
        3'd2: ph_rom_data = 80'h4000_C000000000000000;  // 3.0
        3'd3: ph_rom_data = 80'h4001_8000000000000000;  // 4.0
        3'd4: ph_rom_data = 80'h4001_A000000000000000;  // 5.0
        default: ph_rom_data = 80'd0;
    endcase
end

//============================================================================
// Helper Tasks
//============================================================================

task wait_for_complete;
    input integer max_cycles;
    integer i;
    begin
        for (i = 0; i < max_cycles; i = i + 1) begin
            @(posedge clk);
            if (instruction_complete) begin
                i = max_cycles;
            end
        end
        if (!instruction_complete) begin
            $display("  ERROR: Timeout waiting for instruction_complete");
            timeout_count = timeout_count + 1;
        end
    end
endtask

task test_microprogram;
    input [4:0] prog_index;
    input [79:0] input_data;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        data_in = input_data;
        micro_program_index = prog_index;
        start = 1;
        @(posedge clk);
        start = 0;

        wait_for_complete(1000);  // Wait up to 1000 cycles

        if (instruction_complete) begin
            $display("  Program index: %0d", prog_index);
            $display("  Input:         %h", input_data);
            $display("  Output:        %h", data_out);
            $display("  Temp result:   %h", debug_temp_result);
            pass_count = pass_count + 1;
            $display("  PASS: Microprogram completed");
        end else begin
            $display("  FAIL: Did not complete");
            fail_count = fail_count + 1;
        end

        repeat(5) @(posedge clk);
    end
endtask

//============================================================================
// Test Stimulus
//============================================================================

initial begin
    $display("================================================================");
    $display("MicroSequencer Extended BCD Testbench");
    $display("Testing microcode execution engine");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    timeout_count = 0;

    reset = 1;
    start = 0;
    micro_program_index = 5'd0;
    data_in = 80'd0;
    arith_rounding_mode = 2'b00;  // Round to nearest

    repeat(20) @(posedge clk);
    reset = 0;
    repeat(10) @(posedge clk);

    //========================================================================
    // Test Group 1: Basic Arithmetic Programs
    //========================================================================

    $display("\n========================================");
    $display("Test Group 1: Basic Arithmetic Programs");
    $display("========================================");

    test_microprogram(PROG_FADD, FP80_ONE, "FADD program");
    test_microprogram(PROG_FSUB, FP80_ONE, "FSUB program");
    test_microprogram(PROG_FMUL, FP80_TWO, "FMUL program");
    test_microprogram(PROG_FDIV, FP80_TWO, "FDIV program");

    //========================================================================
    // Test Group 2: Load/Store Programs
    //========================================================================

    $display("\n========================================");
    $display("Test Group 2: Load/Store Programs");
    $display("========================================");

    test_microprogram(PROG_FLD, FP80_ONE, "FLD program");
    test_microprogram(PROG_FST, FP80_ONE, "FST program");

    //========================================================================
    // Test Group 3: Transcendental Programs
    //========================================================================

    $display("\n========================================");
    $display("Test Group 3: Transcendental Programs");
    $display("========================================");

    test_microprogram(PROG_FSQRT, FP80_ONE, "FSQRT program");
    test_microprogram(PROG_FSIN, FP80_ZERO, "FSIN program");
    test_microprogram(PROG_FCOS, FP80_ZERO, "FCOS program");

    //========================================================================
    // Test Group 4: BCD Operations
    //========================================================================

    $display("\n========================================");
    $display("Test Group 4: BCD Operations");
    $display("========================================");

    test_microprogram(PROG_FBLD, FP80_ZERO, "FBLD program");
    test_microprogram(PROG_FBSTP, FP80_ONE, "FBSTP program");

    //========================================================================
    // Test Group 5: Additional Functions
    //========================================================================

    $display("\n========================================");
    $display("Test Group 5: Additional Functions");
    $display("========================================");

    test_microprogram(PROG_FXTRACT, FP80_TWO, "FXTRACT program");
    test_microprogram(PROG_FSCALE, FP80_ONE, "FSCALE program");
    test_microprogram(PROG_FRNDINT, FP80_ONE, "FRNDINT program");

    //========================================================================
    // Summary
    //========================================================================

    repeat(20) @(posedge clk);

    $display("\n================================================================");
    $display("MicroSequencer Extended BCD Testbench Summary");
    $display("================================================================");
    $display("Total tests:  %0d", test_count);
    $display("Passed:       %0d", pass_count);
    $display("Failed:       %0d", fail_count);
    $display("Timeouts:     %0d", timeout_count);
    $display("");

    if (fail_count == 0 && timeout_count == 0) begin
        $display("*** ALL TESTS PASSED ***");
    end else begin
        $display("*** SOME TESTS FAILED ***");
    end

    $display("================================================================");

    $finish;
end

endmodule

`default_nettype wire
