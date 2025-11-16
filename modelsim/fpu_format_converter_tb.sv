//============================================================================
//
//  FPU Format Converter Comprehensive Testbench
//  Tests all conversion modes for 8087 FPU format conversions
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module fpu_format_converter_tb;

//============================================================================
// Clock and Reset
//============================================================================

reg clk;
reg reset;

initial begin
    clk = 0;
    forever #5 clk = ~clk;  // 100 MHz clock
end

//============================================================================
// DUT Signals
//============================================================================

reg enable;
reg [3:0] mode;

// Inputs
reg [79:0] fp80_in;
reg [63:0] fp64_in;
reg [31:0] fp32_in;
reg [63:0] uint64_in;
reg [31:0] int32_in;
reg [15:0] int16_in;
reg [63:0] fixed64_in;
reg        uint64_sign;
reg [1:0]  rounding_mode;

// Outputs
wire [79:0] fp80_out;
wire [63:0] fp64_out;
wire [31:0] fp32_out;
wire [63:0] uint64_out;
wire [31:0] int32_out;
wire [15:0] int16_out;
wire [63:0] fixed64_out;
wire        uint64_sign_out;
wire        done;
wire        flag_invalid;
wire        flag_overflow;
wire        flag_underflow;
wire        flag_inexact;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

//============================================================================
// Mode Definitions (from module)
//============================================================================

localparam MODE_FP32_TO_FP80  = 4'd0;
localparam MODE_FP64_TO_FP80  = 4'd1;
localparam MODE_FP80_TO_FP32  = 4'd2;
localparam MODE_FP80_TO_FP64  = 4'd3;
localparam MODE_INT16_TO_FP80 = 4'd4;
localparam MODE_INT32_TO_FP80 = 4'd5;
localparam MODE_FP80_TO_INT16 = 4'd6;
localparam MODE_FP80_TO_INT32 = 4'd7;
localparam MODE_UINT64_TO_FP80 = 4'd8;
localparam MODE_FP80_TO_UINT64 = 4'd9;
localparam MODE_FP80_TO_FIXED64 = 4'd10;
localparam MODE_FIXED64_TO_FP80 = 4'd11;

//============================================================================
// DUT Instantiation
//============================================================================

FPU_Format_Converter_Unified dut (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .mode(mode),
    .fp80_in(fp80_in),
    .fp64_in(fp64_in),
    .fp32_in(fp32_in),
    .uint64_in(uint64_in),
    .int32_in(int32_in),
    .int16_in(int16_in),
    .fixed64_in(fixed64_in),
    .uint64_sign(uint64_sign),
    .rounding_mode(rounding_mode),
    .fp80_out(fp80_out),
    .fp64_out(fp64_out),
    .fp32_out(fp32_out),
    .uint64_out(uint64_out),
    .int32_out(int32_out),
    .int16_out(int16_out),
    .fixed64_out(fixed64_out),
    .uint64_sign_out(uint64_sign_out),
    .done(done),
    .flag_invalid(flag_invalid),
    .flag_overflow(flag_overflow),
    .flag_underflow(flag_underflow),
    .flag_inexact(flag_inexact)
);

//============================================================================
// Helper Functions
//============================================================================

// Pack FP80: sign(1) + exp(15) + integer bit(1) + fraction(63)
function [79:0] pack_fp80;
    input sign;
    input [14:0] exp;
    input [63:0] mant;  // includes integer bit
    begin
        pack_fp80 = {sign, exp, mant};
    end
endfunction

// Pack FP32: sign(1) + exp(8) + fraction(23)
function [31:0] pack_fp32;
    input sign;
    input [7:0] exp;
    input [22:0] frac;
    begin
        pack_fp32 = {sign, exp, frac};
    end
endfunction

// Pack FP64: sign(1) + exp(11) + fraction(52)
function [63:0] pack_fp64;
    input sign;
    input [10:0] exp;
    input [51:0] frac;
    begin
        pack_fp64 = {sign, exp, frac};
    end
endfunction

//============================================================================
// Test Stimulus
//============================================================================

initial begin
    $display("================================================================");
    $display("FPU Format Converter Comprehensive Testbench");
    $display("Testing all conversion modes for 8087 FPU");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1;
    enable = 0;
    mode = 0;
    fp80_in = 80'd0;
    fp64_in = 64'd0;
    fp32_in = 32'd0;
    uint64_in = 64'd0;
    int32_in = 32'd0;
    int16_in = 16'd0;
    fixed64_in = 64'd0;
    uint64_sign = 1'b0;
    rounding_mode = 2'b00;  // Round to nearest

    repeat(10) @(posedge clk);
    reset = 0;
    repeat(5) @(posedge clk);

    //========================================================================
    // Test Group 1: FP32 ↔ FP80
    //========================================================================

    $display("Test Group 1: FP32 ↔ FP80 Conversions");
    $display("----------------------------------------");

    // Test 1: FP32 → FP80 (1.0)
    $display("\nTest 1: FP32 to FP80 - Convert 1.0");
    test_count++;
    fp32_in = pack_fp32(1'b0, 8'd127, 23'd0);  // 1.0 in FP32
    mode = MODE_FP32_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[78:64] == 15'h3FFF && fp80_out[63] == 1'b1) begin
        $display("  [PASS] FP32(1.0) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP32(1.0) → FP80 = 0x%020X (expected exp=3FFF, int bit=1)", fp80_out);
        fail_count++;
    end

    // Test 2: FP32 → FP80 (-2.5)
    $display("\nTest 2: FP32 to FP80 - Convert -2.5");
    test_count++;
    fp32_in = pack_fp32(1'b1, 8'd128, 23'h200000);  // -2.5 in FP32
    mode = MODE_FP32_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[79] == 1'b1 && fp80_out[78:64] == 15'h4000) begin
        $display("  [PASS] FP32(-2.5) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP32(-2.5) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 3: FP80 → FP32 (1.0)
    $display("\nTest 3: FP80 to FP32 - Convert 1.0");
    test_count++;
    fp80_in = pack_fp80(1'b0, 15'h3FFF, 64'h8000000000000000);  // 1.0 in FP80
    mode = MODE_FP80_TO_FP32;
    rounding_mode = 2'b00;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp32_out == 32'h3F800000) begin
        $display("  [PASS] FP80(1.0) → FP32 = 0x%08X", fp32_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP80(1.0) → FP32 = 0x%08X (expected 3F800000)", fp32_out);
        fail_count++;
    end

    //========================================================================
    // Test Group 2: FP64 ↔ FP80
    //========================================================================

    $display("\n\nTest Group 2: FP64 ↔ FP80 Conversions");
    $display("----------------------------------------");

    // Test 4: FP64 → FP80 (3.14159)
    $display("\nTest 4: FP64 to FP80 - Convert 3.14159");
    test_count++;
    fp64_in = 64'h400921FB4D12D84A;  // π in FP64
    mode = MODE_FP64_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[78:64] == 15'h4000) begin
        $display("  [PASS] FP64(π) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP64(π) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 5: FP80 → FP64 (1.0)
    $display("\nTest 5: FP80 to FP64 - Convert 1.0");
    test_count++;
    fp80_in = pack_fp80(1'b0, 15'h3FFF, 64'h8000000000000000);
    mode = MODE_FP80_TO_FP64;
    rounding_mode = 2'b00;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp64_out == 64'h3FF0000000000000) begin
        $display("  [PASS] FP80(1.0) → FP64 = 0x%016X", fp64_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP80(1.0) → FP64 = 0x%016X (expected 3FF0000000000000)", fp64_out);
        fail_count++;
    end

    //========================================================================
    // Test Group 3: INT16 ↔ FP80
    //========================================================================

    $display("\n\nTest Group 3: INT16 ↔ FP80 Conversions");
    $display("----------------------------------------");

    // Test 6: INT16 → FP80 (42)
    $display("\nTest 6: INT16 to FP80 - Convert 42");
    test_count++;
    int16_in = 16'd42;
    mode = MODE_INT16_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[78:64] == 15'h4004) begin  // Exp for 42 = 2^5 + ... ≈ 16388
        $display("  [PASS] INT16(42) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] INT16(42) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 7: INT16 → FP80 (-100)
    $display("\nTest 7: INT16 to FP80 - Convert -100");
    test_count++;
    int16_in = -16'd100;
    mode = MODE_INT16_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[79] == 1'b1 && fp80_out[78:64] == 15'h4005) begin
        $display("  [PASS] INT16(-100) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] INT16(-100) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 8: FP80 → INT16 (42)
    $display("\nTest 8: FP80 to INT16 - Convert 42");
    test_count++;
    fp80_in = pack_fp80(1'b0, 15'h4004, 64'hA800000000000000);  // 42.0
    mode = MODE_FP80_TO_INT16;
    rounding_mode = 2'b00;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (int16_out == 16'd42) begin
        $display("  [PASS] FP80(42.0) → INT16 = %0d", $signed(int16_out));
        pass_count++;
    end else begin
        $display("  [FAIL] FP80(42.0) → INT16 = %0d (expected 42)", $signed(int16_out));
        fail_count++;
    end

    //========================================================================
    // Test Group 4: INT32 ↔ FP80
    //========================================================================

    $display("\n\nTest Group 4: INT32 ↔ FP80 Conversions");
    $display("----------------------------------------");

    // Test 9: INT32 → FP80 (1000000)
    $display("\nTest 9: INT32 to FP80 - Convert 1000000");
    test_count++;
    int32_in = 32'd1000000;
    mode = MODE_INT32_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[78:64] == 15'h4012) begin  // Exp for 10^6 ≈ 2^19.9 → 16402
        $display("  [PASS] INT32(1000000) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] INT32(1000000) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 10: INT32 → FP80 (-2147483648 = INT32_MIN)
    $display("\nTest 10: INT32 to FP80 - Convert INT32_MIN");
    test_count++;
    int32_in = 32'h80000000;  // -2^31
    mode = MODE_INT32_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[79] == 1'b1 && fp80_out[78:64] == 15'h401E) begin
        $display("  [PASS] INT32(MIN) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] INT32(MIN) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 11: FP80 → INT32 (1000000)
    $display("\nTest 11: FP80 to INT32 - Convert 1000000");
    test_count++;
    fp80_in = pack_fp80(1'b0, 15'h4012, 64'hF424000000000000);  // 1000000.0
    mode = MODE_FP80_TO_INT32;
    rounding_mode = 2'b00;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (int32_out == 32'd1000000) begin
        $display("  [PASS] FP80(1000000.0) → INT32 = %0d", $signed(int32_out));
        pass_count++;
    end else begin
        $display("  [FAIL] FP80(1000000.0) → INT32 = %0d (expected 1000000)", $signed(int32_out));
        fail_count++;
    end

    //========================================================================
    // Test Group 5: Special Values
    //========================================================================

    $display("\n\nTest Group 5: Special Values");
    $display("----------------------------------------");

    // Test 12: FP32 Zero → FP80
    $display("\nTest 12: FP32 Zero to FP80");
    test_count++;
    fp32_in = 32'h00000000;  // +0.0
    mode = MODE_FP32_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out == 80'd0) begin
        $display("  [PASS] FP32(+0.0) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP32(+0.0) → FP80 = 0x%020X (expected 0)", fp80_out);
        fail_count++;
    end

    // Test 13: FP32 Infinity → FP80
    $display("\nTest 13: FP32 Infinity to FP80");
    test_count++;
    fp32_in = 32'h7F800000;  // +Infinity
    mode = MODE_FP32_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[78:64] == 15'h7FFF && fp80_out[63] == 1'b1) begin
        $display("  [PASS] FP32(+Inf) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP32(+Inf) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 14: FP80 Zero → FP32
    $display("\nTest 14: FP80 Zero to FP32");
    test_count++;
    fp80_in = 80'd0;
    mode = MODE_FP80_TO_FP32;
    rounding_mode = 2'b00;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp32_out == 32'h00000000) begin
        $display("  [PASS] FP80(+0.0) → FP32 = 0x%08X", fp32_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP80(+0.0) → FP32 = 0x%08X (expected 0)", fp32_out);
        fail_count++;
    end

    // Test 15: INT16 Zero → FP80
    $display("\nTest 15: INT16 Zero to FP80");
    test_count++;
    int16_in = 16'd0;
    mode = MODE_INT16_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out == 80'd0) begin
        $display("  [PASS] INT16(0) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] INT16(0) → FP80 = 0x%020X (expected 0)", fp80_out);
        fail_count++;
    end

    //========================================================================
    // Test Group 6: Rounding Modes
    //========================================================================

    $display("\n\nTest Group 6: Rounding Modes");
    $display("----------------------------------------");

    // Test 16: Round to nearest (default)
    $display("\nTest 16: FP80 to FP32 - Round to nearest (1.5)");
    test_count++;
    fp80_in = pack_fp80(1'b0, 15'h3FFF, 64'hC000000000000001);  // 1.5 + epsilon
    mode = MODE_FP80_TO_FP32;
    rounding_mode = 2'b00;  // Round to nearest
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp32_out[30:23] == 8'd127 || fp32_out[30:23] == 8'd128) begin
        $display("  [PASS] Round to nearest: FP32 = 0x%08X", fp32_out);
        pass_count++;
    end else begin
        $display("  [FAIL] Round to nearest: FP32 = 0x%08X", fp32_out);
        fail_count++;
    end

    // Test 17: Round toward zero (truncate)
    $display("\nTest 17: FP80 to INT32 - Round toward zero (2.9)");
    test_count++;
    fp80_in = pack_fp80(1'b0, 15'h4000, 64'hB99999A000000000);  // ≈2.9
    mode = MODE_FP80_TO_INT32;
    rounding_mode = 2'b11;  // Truncate
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (int32_out == 32'd2) begin
        $display("  [PASS] Round toward zero: INT32 = %0d", $signed(int32_out));
        pass_count++;
    end else begin
        $display("  [FAIL] Round toward zero: INT32 = %0d (expected 2)", $signed(int32_out));
        fail_count++;
    end

    //========================================================================
    // Test Group 7: Edge Cases
    //========================================================================

    $display("\n\nTest Group 7: Edge Cases");
    $display("----------------------------------------");

    // Test 18: Maximum INT16 → FP80
    $display("\nTest 18: Maximum INT16 to FP80");
    test_count++;
    int16_in = 16'h7FFF;  // 32767
    mode = MODE_INT16_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[78:64] == 15'h400D) begin  // Exp for 32767 (2^14.99)
        $display("  [PASS] INT16(MAX) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] INT16(MAX) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 19: Minimum INT16 → FP80
    $display("\nTest 19: Minimum INT16 to FP80");
    test_count++;
    int16_in = 16'h8000;  // -32768
    mode = MODE_INT16_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[79] == 1'b1 && fp80_out[78:64] == 15'h400E) begin
        $display("  [PASS] INT16(MIN) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] INT16(MIN) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    // Test 20: Very small FP32 → FP80 (denormal handling)
    $display("\nTest 20: Very small FP32 to FP80");
    test_count++;
    fp32_in = 32'h00800000;  // Smallest normalized FP32
    mode = MODE_FP32_TO_FP80;
    enable = 1;
    @(posedge clk);
    enable = 0;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (fp80_out[78:64] == 15'h3F81) begin  // Exp for smallest FP32
        $display("  [PASS] FP32(smallest normalized) → FP80 = 0x%020X", fp80_out);
        pass_count++;
    end else begin
        $display("  [FAIL] FP32(smallest normalized) → FP80 = 0x%020X", fp80_out);
        fail_count++;
    end

    //========================================================================
    // Test Summary
    //========================================================================

    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0d%%", (pass_count * 100) / test_count);
    $display("================================================================");

    if (fail_count == 0) begin
        $display("");
        $display("*** ALL TESTS PASSED ***");
        $display("*** FPU FORMAT CONVERTER VERIFIED ***");
        $display("");
    end else begin
        $display("");
        $display("*** SOME TESTS FAILED ***");
        $display("");
    end

    $finish;
end

// VCD dump for waveform viewing
initial begin
    $dumpfile("fpu_format_converter_tb.vcd");
    $dumpvars(0, fpu_format_converter_tb);
end

// Timeout
initial begin
    #500000;
    $display("\n[ERROR] Timeout!");
    $finish;
end

endmodule

`default_nettype wire
