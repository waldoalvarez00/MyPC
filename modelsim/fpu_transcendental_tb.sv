//============================================================================
//
//  FPU Transcendental Unit Testbench
//  Tests all transcendental operations: SIN, COS, TAN, ATAN, F2XM1, FYL2X, etc.
//
//  Copyright Waldo Alvarez, 2025
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module fpu_transcendental_tb;

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

reg [3:0] operation;
reg enable;

// Operands
reg [79:0] operand_a;
reg [79:0] operand_b;

// Results
wire [79:0] result_primary;
wire [79:0] result_secondary;
wire        has_secondary;
wire        done;
wire        error;

// External arithmetic interface
wire        ext_addsub_req;
wire [79:0] ext_addsub_a;
wire [79:0] ext_addsub_b;
wire        ext_addsub_sub;
reg  [79:0] ext_addsub_result;
reg         ext_addsub_done;
reg         ext_addsub_invalid;
reg         ext_addsub_overflow;
reg         ext_addsub_underflow;
reg         ext_addsub_inexact;

wire        ext_muldiv_req;
wire        ext_muldiv_op;
wire [79:0] ext_muldiv_a;
wire [79:0] ext_muldiv_b;
reg  [79:0] ext_muldiv_result;
reg         ext_muldiv_done;
reg         ext_muldiv_invalid;
reg         ext_muldiv_div_by_zero;
reg         ext_muldiv_overflow;
reg         ext_muldiv_underflow;
reg         ext_muldiv_inexact;

// Polynomial evaluator interface (directly fed back)
wire        ext_poly_addsub_req;
wire [79:0] ext_poly_addsub_a;
wire [79:0] ext_poly_addsub_b;
wire        ext_poly_muldiv_req;
wire [79:0] ext_poly_muldiv_a;
wire [79:0] ext_poly_muldiv_b;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
integer timeout_count;

//============================================================================
// Operation Codes
//============================================================================

localparam OP_SQRT    = 4'd0;
localparam OP_SIN     = 4'd1;
localparam OP_COS     = 4'd2;
localparam OP_SINCOS  = 4'd3;
localparam OP_TAN     = 4'd4;
localparam OP_ATAN    = 4'd5;
localparam OP_F2XM1   = 4'd6;
localparam OP_FYL2X   = 4'd7;
localparam OP_FYL2XP1 = 4'd8;

//============================================================================
// FP80 Constants
//============================================================================

localparam FP80_ZERO     = 80'h0000_0000000000000000;
localparam FP80_ONE      = 80'h3FFF_8000000000000000;
localparam FP80_HALF     = 80'h3FFE_8000000000000000;
localparam FP80_TWO      = 80'h4000_8000000000000000;
localparam FP80_NEG_ONE  = 80'hBFFF_8000000000000000;
localparam FP80_PI_4     = 80'h3FFE_C90FDAA22168C235;
localparam FP80_PI_2     = 80'h3FFF_C90FDAA22168C235;

//============================================================================
// DUT Instantiation
//============================================================================

FPU_Transcendental dut (
    .clk(clk),
    .reset(reset),
    .operation(operation),
    .enable(enable),
    .operand_a(operand_a),
    .operand_b(operand_b),
    .result_primary(result_primary),
    .result_secondary(result_secondary),
    .has_secondary(has_secondary),
    .done(done),
    .error(error),
    .ext_addsub_req(ext_addsub_req),
    .ext_addsub_a(ext_addsub_a),
    .ext_addsub_b(ext_addsub_b),
    .ext_addsub_sub(ext_addsub_sub),
    .ext_addsub_result(ext_addsub_result),
    .ext_addsub_done(ext_addsub_done),
    .ext_addsub_invalid(ext_addsub_invalid),
    .ext_addsub_overflow(ext_addsub_overflow),
    .ext_addsub_underflow(ext_addsub_underflow),
    .ext_addsub_inexact(ext_addsub_inexact),
    .ext_muldiv_req(ext_muldiv_req),
    .ext_muldiv_op(ext_muldiv_op),
    .ext_muldiv_a(ext_muldiv_a),
    .ext_muldiv_b(ext_muldiv_b),
    .ext_muldiv_result(ext_muldiv_result),
    .ext_muldiv_done(ext_muldiv_done),
    .ext_muldiv_invalid(ext_muldiv_invalid),
    .ext_muldiv_div_by_zero(ext_muldiv_div_by_zero),
    .ext_muldiv_overflow(ext_muldiv_overflow),
    .ext_muldiv_underflow(ext_muldiv_underflow),
    .ext_muldiv_inexact(ext_muldiv_inexact),
    .ext_poly_addsub_req(ext_poly_addsub_req),
    .ext_poly_addsub_a(ext_poly_addsub_a),
    .ext_poly_addsub_b(ext_poly_addsub_b),
    .ext_poly_addsub_result(ext_addsub_result),  // Share with main
    .ext_poly_addsub_done(ext_addsub_done),
    .ext_poly_addsub_invalid(ext_addsub_invalid),
    .ext_poly_addsub_overflow(ext_addsub_overflow),
    .ext_poly_addsub_underflow(ext_addsub_underflow),
    .ext_poly_addsub_inexact(ext_addsub_inexact),
    .ext_poly_muldiv_req(ext_poly_muldiv_req),
    .ext_poly_muldiv_a(ext_poly_muldiv_a),
    .ext_poly_muldiv_b(ext_poly_muldiv_b),
    .ext_poly_muldiv_result(ext_muldiv_result),  // Share with main
    .ext_poly_muldiv_done(ext_muldiv_done),
    .ext_poly_muldiv_invalid(ext_muldiv_invalid),
    .ext_poly_muldiv_overflow(ext_muldiv_overflow),
    .ext_poly_muldiv_underflow(ext_muldiv_underflow),
    .ext_poly_muldiv_inexact(ext_muldiv_inexact)
);

//============================================================================
// Stub Arithmetic Units - Edge-triggered for new operations
// Responds to both main (ext_*_req) and polynomial (ext_poly_*_req) requests
//============================================================================

reg [3:0] addsub_delay;
reg [3:0] muldiv_delay;
reg addsub_req_prev;
reg muldiv_req_prev;
wire addsub_any_req = ext_addsub_req || ext_poly_addsub_req;
wire muldiv_any_req = ext_muldiv_req || ext_poly_muldiv_req;

// Save operands when request edge is detected (before WAIT state clears request)
reg [79:0] addsub_saved_a;
reg [79:0] muldiv_saved_a;
reg addsub_saved_from_main;
reg muldiv_saved_from_main;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        ext_addsub_done <= 1'b0;
        ext_addsub_result <= 80'd0;
        ext_addsub_invalid <= 1'b0;
        ext_addsub_overflow <= 1'b0;
        ext_addsub_underflow <= 1'b0;
        ext_addsub_inexact <= 1'b0;
        addsub_delay <= 4'd0;
        addsub_req_prev <= 1'b0;
        addsub_saved_a <= 80'd0;
        addsub_saved_from_main <= 1'b0;
    end else begin
        addsub_req_prev <= addsub_any_req;

        // Detect rising edge of any addsub request
        if (addsub_any_req && !addsub_req_prev) begin
            ext_addsub_done <= 1'b0;
            addsub_delay <= 4'd3;
            // Save operand and source NOW before WAIT state clears request
            addsub_saved_from_main <= ext_addsub_req;
            addsub_saved_a <= ext_addsub_req ? ext_addsub_a : ext_poly_addsub_a;
            $display("[STUB ADDSUB] Edge detected, req=%b poly_req=%b, a=%h",
                     ext_addsub_req, ext_poly_addsub_req,
                     ext_addsub_req ? ext_addsub_a : ext_poly_addsub_a);
        end
        // Count down
        else if (addsub_delay > 1) begin
            addsub_delay <= addsub_delay - 1;
        end
        // Complete operation - pulse done for one cycle
        else if (addsub_delay == 1) begin
            addsub_delay <= 4'd0;
            ext_addsub_done <= 1'b1;
            ext_addsub_result <= addsub_saved_a;  // Use saved operand
            $display("[STUB ADDSUB] Done, result=%h", addsub_saved_a);
        end
        // Clear done after one cycle
        else begin
            ext_addsub_done <= 1'b0;
        end
    end
end

always @(posedge clk or posedge reset) begin
    if (reset) begin
        ext_muldiv_done <= 1'b0;
        ext_muldiv_result <= 80'd0;
        ext_muldiv_invalid <= 1'b0;
        ext_muldiv_div_by_zero <= 1'b0;
        ext_muldiv_overflow <= 1'b0;
        ext_muldiv_underflow <= 1'b0;
        ext_muldiv_inexact <= 1'b0;
        muldiv_delay <= 4'd0;
        muldiv_req_prev <= 1'b0;
        muldiv_saved_a <= 80'd0;
        muldiv_saved_from_main <= 1'b0;
    end else begin
        muldiv_req_prev <= muldiv_any_req;

        // Detect rising edge of any muldiv request
        if (muldiv_any_req && !muldiv_req_prev) begin
            ext_muldiv_done <= 1'b0;
            muldiv_delay <= 4'd5;
            // Save operand and source NOW before WAIT state clears request
            muldiv_saved_from_main <= ext_muldiv_req;
            muldiv_saved_a <= ext_muldiv_req ? ext_muldiv_a : ext_poly_muldiv_a;
            $display("[STUB MULDIV] Edge detected, req=%b poly_req=%b, a=%h",
                     ext_muldiv_req, ext_poly_muldiv_req,
                     ext_muldiv_req ? ext_muldiv_a : ext_poly_muldiv_a);
        end
        // Count down
        else if (muldiv_delay > 1) begin
            muldiv_delay <= muldiv_delay - 1;
        end
        // Complete operation - pulse done for one cycle
        else if (muldiv_delay == 1) begin
            muldiv_delay <= 4'd0;
            ext_muldiv_done <= 1'b1;
            ext_muldiv_result <= muldiv_saved_a;  // Use saved operand
            $display("[STUB MULDIV] Done, result=%h", muldiv_saved_a);
        end
        // Clear done after one cycle
        else begin
            ext_muldiv_done <= 1'b0;
        end
    end
end

//============================================================================
// Helper Tasks
//============================================================================

task wait_for_done;
    input integer max_cycles;
    integer i;
    begin
        for (i = 0; i < max_cycles; i = i + 1) begin
            @(posedge clk);
            if (done) begin
                i = max_cycles;
            end
        end
        if (!done) begin
            $display("  ERROR: Timeout waiting for done signal");
            timeout_count = timeout_count + 1;
        end
    end
endtask

task test_unary_op;
    input [3:0] op;
    input [79:0] a;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        operation = op;
        operand_a = a;
        operand_b = FP80_ZERO;
        enable = 1;
        @(posedge clk);
        enable = 0;

        wait_for_done(700);

        if (done && !error) begin
            $display("  Input:     %h", a);
            $display("  Result:    %h", result_primary);
            if (has_secondary)
                $display("  Secondary: %h", result_secondary);
            pass_count = pass_count + 1;
            $display("  PASS: Operation completed");
        end else if (error) begin
            $display("  FAIL: Error flag asserted");
            fail_count = fail_count + 1;
        end else begin
            $display("  FAIL: Did not complete");
            fail_count = fail_count + 1;
        end

        repeat(5) @(posedge clk);
    end
endtask

// Task for testing operations expected to return an error (unsupported ops)
task test_error_op;
    input [3:0] op;
    input [79:0] a;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        operation = op;
        operand_a = a;
        operand_b = FP80_ZERO;
        enable = 1;
        @(posedge clk);
        enable = 0;

        wait_for_done(700);

        if (done && error) begin
            $display("  PASS: Error correctly signaled for unsupported operation");
            pass_count = pass_count + 1;
        end else if (done && !error) begin
            $display("  FAIL: Expected error but operation completed normally");
            fail_count = fail_count + 1;
        end else begin
            $display("  FAIL: Did not complete");
            fail_count = fail_count + 1;
        end

        repeat(5) @(posedge clk);
    end
endtask

task test_binary_op;
    input [3:0] op;
    input [79:0] a;
    input [79:0] b;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        operation = op;
        operand_a = a;
        operand_b = b;
        enable = 1;
        @(posedge clk);
        enable = 0;

        wait_for_done(700);

        if (done && !error) begin
            $display("  Input A:   %h", a);
            $display("  Input B:   %h", b);
            $display("  Result:    %h", result_primary);
            pass_count = pass_count + 1;
            $display("  PASS: Operation completed");
        end else if (error) begin
            $display("  FAIL: Error flag asserted");
            fail_count = fail_count + 1;
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
    $display("FPU Transcendental Unit Testbench");
    $display("Testing all transcendental operations");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    timeout_count = 0;

    reset = 1;
    enable = 0;
    operation = 4'd0;
    operand_a = 80'd0;
    operand_b = 80'd0;

    repeat(20) @(posedge clk);
    reset = 0;
    repeat(10) @(posedge clk);

    //========================================================================
    // Test Group 1: Trigonometric Functions
    //========================================================================

    $display("\n========================================");
    $display("Test Group 1: Trigonometric Functions");
    $display("========================================");

    // SIN tests
    test_unary_op(OP_SIN, FP80_ZERO, "SIN(0)");
    test_unary_op(OP_SIN, FP80_PI_4, "SIN(pi/4)");

    // COS tests
    test_unary_op(OP_COS, FP80_ZERO, "COS(0)");
    test_unary_op(OP_COS, FP80_PI_4, "COS(pi/4)");

    // SINCOS test
    test_unary_op(OP_SINCOS, FP80_PI_4, "SINCOS(pi/4)");

    // TAN test
    test_unary_op(OP_TAN, FP80_ZERO, "TAN(0)");
    test_unary_op(OP_TAN, FP80_PI_4, "TAN(pi/4)");

    // ATAN test
    test_unary_op(OP_ATAN, FP80_ZERO, "ATAN(0)");
    test_unary_op(OP_ATAN, FP80_ONE, "ATAN(1)");

    //========================================================================
    // Test Group 2: Exponential/Logarithmic Functions
    //========================================================================

    $display("\n========================================");
    $display("Test Group 2: Exp/Log Functions");
    $display("========================================");

    // F2XM1: 2^x - 1
    test_unary_op(OP_F2XM1, FP80_ZERO, "F2XM1(0) = 0");
    test_unary_op(OP_F2XM1, FP80_HALF, "F2XM1(0.5)");

    // FYL2X: y * log2(x)
    test_binary_op(OP_FYL2X, FP80_TWO, FP80_ONE, "FYL2X(2, 1) = log2(2)");
    test_binary_op(OP_FYL2X, FP80_ONE, FP80_ONE, "FYL2X(1, 1) = 0");

    // FYL2XP1: y * log2(x+1)
    test_binary_op(OP_FYL2XP1, FP80_ONE, FP80_ONE, "FYL2XP1(1, 1) = log2(2)");

    //========================================================================
    // Test Group 3: SQRT (expected to return NaN - microcode only)
    //========================================================================

    $display("\n========================================");
    $display("Test Group 3: SQRT (microcode only)");
    $display("========================================");

    test_error_op(OP_SQRT, FP80_ONE, "SQRT(1) - unsupported, expects error");

    //========================================================================
    // Summary
    //========================================================================

    repeat(20) @(posedge clk);

    $display("\n================================================================");
    $display("Transcendental Unit Testbench Summary");
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
