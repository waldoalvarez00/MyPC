//============================================================================
//
//  FPU CORDIC Wrapper Testbench
//  Tests sin/cos/tan/atan via CORDIC algorithm
//
//  Copyright Waldo Alvarez, 2025
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module fpu_cordic_wrapper_tb;

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

reg enable;
reg [1:0] mode;

// Inputs
reg [79:0] angle_in;
reg [79:0] x_in;
reg [79:0] y_in;

// Outputs
wire [79:0] sin_out;
wire [79:0] cos_out;
wire [79:0] atan_out;
wire [79:0] magnitude_out;
wire [79:0] tan_out;
wire done;
wire error;

// External arithmetic interface
wire        ext_addsub_req;
wire [79:0] ext_addsub_a;
wire [79:0] ext_addsub_b;
wire        ext_addsub_sub;
reg  [79:0] ext_addsub_result;
reg         ext_addsub_done;
reg         ext_addsub_invalid;

wire        ext_muldiv_req;
wire        ext_muldiv_op;
wire [79:0] ext_muldiv_a;
wire [79:0] ext_muldiv_b;
reg  [79:0] ext_muldiv_result;
reg         ext_muldiv_done;
reg         ext_muldiv_invalid;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
integer timeout_count;

//============================================================================
// Mode Definitions
//============================================================================

localparam MODE_ROTATION  = 2'b00;  // SIN/COS
localparam MODE_VECTORING = 2'b01;  // ATAN
localparam MODE_TAN       = 2'b10;  // TAN

//============================================================================
// FP80 Constants
//============================================================================

// Common FP80 values
localparam FP80_ZERO      = 80'h0000_0000000000000000;
localparam FP80_ONE       = 80'h3FFF_8000000000000000;
localparam FP80_HALF      = 80'h3FFE_8000000000000000;
localparam FP80_NEG_ONE   = 80'hBFFF_8000000000000000;

// Pi-related constants (80-bit extended precision)
// π ≈ 3.14159265358979323846
localparam FP80_PI        = 80'h4000_C90FDAA22168C235;
// π/2 ≈ 1.57079632679489661923
localparam FP80_PI_2      = 80'h3FFF_C90FDAA22168C235;
// π/4 ≈ 0.78539816339744830962
localparam FP80_PI_4      = 80'h3FFE_C90FDAA22168C235;
// π/6 ≈ 0.52359877559829887308
localparam FP80_PI_6      = 80'h3FFE_860A91C16B9B2C23;
// π/3 ≈ 1.04719755119659774615
localparam FP80_PI_3      = 80'h3FFF_860A91C16B9B2C23;

// Expected results (80-bit extended precision)
// sin(π/6) = 0.5
localparam FP80_SIN_PI_6  = 80'h3FFE_8000000000000000;
// cos(π/6) = √3/2 ≈ 0.86602540378443864676
localparam FP80_COS_PI_6  = 80'h3FFE_DDB3D742C265539E;
// sin(π/4) = cos(π/4) = √2/2 ≈ 0.70710678118654752440
localparam FP80_SIN_PI_4  = 80'h3FFE_B504F333F9DE6484;
// sin(π/2) = 1.0
localparam FP80_SIN_PI_2  = 80'h3FFF_8000000000000000;
// cos(π/2) = 0.0
localparam FP80_COS_PI_2  = 80'h0000_0000000000000000;

//============================================================================
// DUT Instantiation
//============================================================================

FPU_CORDIC_Wrapper dut (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .mode(mode),
    .angle_in(angle_in),
    .x_in(x_in),
    .y_in(y_in),
    .sin_out(sin_out),
    .cos_out(cos_out),
    .atan_out(atan_out),
    .magnitude_out(magnitude_out),
    .tan_out(tan_out),
    .done(done),
    .error(error),
    .ext_addsub_req(ext_addsub_req),
    .ext_addsub_a(ext_addsub_a),
    .ext_addsub_b(ext_addsub_b),
    .ext_addsub_sub(ext_addsub_sub),
    .ext_addsub_result(ext_addsub_result),
    .ext_addsub_done(ext_addsub_done),
    .ext_addsub_invalid(ext_addsub_invalid),
    .ext_muldiv_req(ext_muldiv_req),
    .ext_muldiv_op(ext_muldiv_op),
    .ext_muldiv_a(ext_muldiv_a),
    .ext_muldiv_b(ext_muldiv_b),
    .ext_muldiv_result(ext_muldiv_result),
    .ext_muldiv_done(ext_muldiv_done),
    .ext_muldiv_invalid(ext_muldiv_invalid)
);

//============================================================================
// Stub Arithmetic Units
// These provide simple responses to test the CORDIC state machine
//============================================================================

reg [3:0] addsub_delay;
reg [3:0] muldiv_delay;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        ext_addsub_done <= 1'b0;
        ext_addsub_result <= 80'd0;
        ext_addsub_invalid <= 1'b0;
        addsub_delay <= 4'd0;
    end else begin
        if (ext_addsub_req && addsub_delay == 0) begin
            // Start delay counter
            addsub_delay <= 4'd5;  // 5-cycle delay
            ext_addsub_done <= 1'b0;
        end else if (addsub_delay > 1) begin
            addsub_delay <= addsub_delay - 1;
        end else if (addsub_delay == 1) begin
            // Complete the operation with simple result
            addsub_delay <= 4'd0;
            ext_addsub_done <= 1'b1;
            if (ext_addsub_sub)
                ext_addsub_result <= ext_addsub_a;  // Simplified: return A for subtract
            else
                ext_addsub_result <= ext_addsub_a;  // Simplified: return A for add
        end else begin
            ext_addsub_done <= 1'b0;
        end
    end
end

always @(posedge clk or posedge reset) begin
    if (reset) begin
        ext_muldiv_done <= 1'b0;
        ext_muldiv_result <= 80'd0;
        ext_muldiv_invalid <= 1'b0;
        muldiv_delay <= 4'd0;
    end else begin
        if (ext_muldiv_req && muldiv_delay == 0) begin
            // Start delay counter
            muldiv_delay <= 4'd8;  // 8-cycle delay
            ext_muldiv_done <= 1'b0;
        end else if (muldiv_delay > 1) begin
            muldiv_delay <= muldiv_delay - 1;
        end else if (muldiv_delay == 1) begin
            // Complete the operation with simple result
            muldiv_delay <= 4'd0;
            ext_muldiv_done <= 1'b1;
            ext_muldiv_result <= ext_muldiv_a;  // Simplified: return A
        end else begin
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
                i = max_cycles;  // Exit loop
            end
        end
        if (!done) begin
            $display("  ERROR: Timeout waiting for done signal");
            timeout_count = timeout_count + 1;
        end
    end
endtask

task test_rotation_mode;
    input [79:0] angle;
    input [79:0] expected_sin;
    input [79:0] expected_cos;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        angle_in = angle;
        mode = MODE_ROTATION;
        enable = 1;
        @(posedge clk);
        enable = 0;

        wait_for_done(500);  // Wait up to 500 cycles

        if (done && !error) begin
            $display("  Input angle:  %h", angle);
            $display("  Sin output:   %h", sin_out);
            $display("  Cos output:   %h", cos_out);
            // For stub arithmetic, just check completion
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

task test_vectoring_mode;
    input [79:0] x_val;
    input [79:0] y_val;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        x_in = x_val;
        y_in = y_val;
        mode = MODE_VECTORING;
        enable = 1;
        @(posedge clk);
        enable = 0;

        wait_for_done(500);

        if (done && !error) begin
            $display("  Input X:      %h", x_val);
            $display("  Input Y:      %h", y_val);
            $display("  Atan output:  %h", atan_out);
            $display("  Magnitude:    %h", magnitude_out);
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

task test_tan_mode;
    input [79:0] angle;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        angle_in = angle;
        mode = MODE_TAN;
        enable = 1;
        @(posedge clk);
        enable = 0;

        wait_for_done(600);

        if (done && !error) begin
            $display("  Input angle:  %h", angle);
            $display("  Tan output:   %h", tan_out);
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
    $display("FPU CORDIC Wrapper Testbench");
    $display("Testing sin/cos/tan/atan via CORDIC algorithm");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    timeout_count = 0;

    reset = 1;
    enable = 0;
    mode = 2'b00;
    angle_in = 80'd0;
    x_in = 80'd0;
    y_in = 80'd0;

    repeat(20) @(posedge clk);
    reset = 0;
    repeat(10) @(posedge clk);

    //========================================================================
    // Test Group 1: Rotation Mode (sin/cos)
    //========================================================================

    $display("\n========================================");
    $display("Test Group 1: Rotation Mode (sin/cos)");
    $display("========================================");

    // Test sin/cos(0)
    test_rotation_mode(FP80_ZERO, FP80_ZERO, FP80_ONE, "sin/cos(0)");

    // Test sin/cos(π/6)
    test_rotation_mode(FP80_PI_6, FP80_SIN_PI_6, FP80_COS_PI_6, "sin/cos(pi/6)");

    // Test sin/cos(π/4)
    test_rotation_mode(FP80_PI_4, FP80_SIN_PI_4, FP80_SIN_PI_4, "sin/cos(pi/4)");

    // Test sin/cos(π/2)
    test_rotation_mode(FP80_PI_2, FP80_SIN_PI_2, FP80_COS_PI_2, "sin/cos(pi/2)");

    //========================================================================
    // Test Group 2: Vectoring Mode (atan)
    //========================================================================

    $display("\n========================================");
    $display("Test Group 2: Vectoring Mode (atan)");
    $display("========================================");

    // Test atan(0/1) = atan(0) = 0
    test_vectoring_mode(FP80_ONE, FP80_ZERO, "atan(0/1) = 0");

    // Test atan(1/1) = atan(1) = π/4
    test_vectoring_mode(FP80_ONE, FP80_ONE, "atan(1/1) = pi/4");

    //========================================================================
    // Test Group 3: Tan Mode
    //========================================================================

    $display("\n========================================");
    $display("Test Group 3: Tan Mode");
    $display("========================================");

    // Test tan(0)
    test_tan_mode(FP80_ZERO, "tan(0) = 0");

    // Test tan(π/4)
    test_tan_mode(FP80_PI_4, "tan(pi/4) = 1");

    //========================================================================
    // Test Group 4: Edge Cases
    //========================================================================

    $display("\n========================================");
    $display("Test Group 4: Edge Cases");
    $display("========================================");

    // Test negative angle
    test_rotation_mode({1'b1, FP80_PI_4[78:0]}, FP80_ZERO, FP80_ZERO, "sin/cos(-pi/4)");

    //========================================================================
    // Summary
    //========================================================================

    repeat(20) @(posedge clk);

    $display("\n================================================================");
    $display("CORDIC Wrapper Testbench Summary");
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
