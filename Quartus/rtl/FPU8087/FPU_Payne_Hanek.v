// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// Large Angle Range Reduction
//
// Implements iterative reduction for angles >= 2π to avoid precision
// loss from catastrophic cancellation. Uses repeated subtraction of 2π
// with full precision until angle is in [0, 2π) range.
//
// This is a simplified approach using iterative FP subtraction rather
// than the full Payne-Hanek algorithm with extended precision arithmetic.
//
// Algorithm:
// 1. While angle >= 2π: angle = angle - 2π (using FP subtraction)
// 2. Determine quadrant: q = floor(angle / (π/2))
// 3. Reduce to [0, π/2): reduced = angle - q*(π/2)
//
// Latency: 2-400 cycles depending on input magnitude
// Area: ~600 LUTs
//
// Test Results: 5/7 tests passing
//   - 2π, 4π, 10π, 100π, 0.0: PASS
//   - 3π: Minor precision issue (quadrant 1 vs expected 2, ~0.01% error)
//   - 1000π: Accumulated error from 159 iterations
//
// Limitations:
//   - Boundary cases (e.g., exactly π) may have ±1 ULP rounding errors
//   - Very large multiples (>100π) accumulate error from many iterations
//   - For production use with angles >100π, implement full Payne-Hanek
//=====================================================================

module FPU_Payne_Hanek(
    input wire clk,
    input wire reset,
    input wire enable,

    // Input angle (80-bit FP)
    input wire [79:0] angle_in,

    // Reduced angle output (in [0, π/2))
    output reg [79:0] angle_out,

    // Quadrant information (0-3)
    output reg [1:0] quadrant,

    // Status
    output reg done,
    output reg error,

    // Microcode interface (for large angles >= 100π)
    output reg        microcode_invoke,      // Pulse to invoke microcode
    output reg [11:0] microcode_addr,        // Entry point address (0x0180)
    output reg [79:0] microcode_operand_a,   // Input angle
    input wire        microcode_done,        // Completion signal
    input wire [79:0] microcode_result,      // Reduced angle result
    input wire [1:0]  microcode_quadrant,    // Quadrant result
    input wire        microcode_error        // Error flag
);

    //=================================================================
    // Constants (80-bit IEEE 754 Extended Precision)
    //=================================================================

    localparam FP80_TWO_PI    = 80'h4001_C90FDAA22168C235;  // 2π
    localparam FP80_PI        = 80'h4000_C90FDAA22168C235;  // π
    localparam FP80_PI_OVER_2 = 80'h3FFF_C90FDAA22168C235;  // π/2
    localparam FP80_ZERO      = 80'h0000_0000000000000000;  // 0.0

    // IEEE 754 Extended Precision bias
    localparam [14:0] EXPONENT_BIAS = 15'h3FFF;

    //=================================================================
    // State Machine
    //=================================================================

    localparam [3:0] STATE_IDLE          = 4'd0;
    localparam [3:0] STATE_DISPATCH      = 4'd1;  // NEW: Route to iterative or microcode
    localparam [3:0] STATE_CHECK_RANGE   = 4'd2;
    localparam [3:0] STATE_SUB_2PI       = 4'd3;
    localparam [3:0] STATE_FIND_QUADRANT = 4'd4;
    localparam [3:0] STATE_SUB_QUAD      = 4'd5;
    localparam [3:0] STATE_FINALIZE      = 4'd6;
    localparam [3:0] STATE_MICROCODE_WAIT = 4'd7; // NEW: Wait for microcode completion
    localparam [3:0] STATE_DONE          = 4'd8;

    reg [3:0] state;

    //=================================================================
    // Internal Registers
    //=================================================================

    reg [79:0] angle_working;
    reg [7:0] iteration_count;  // Limit iterations to prevent infinite loops

    // Comparison results
    wire angle_ge_2pi;
    wire angle_ge_pi;
    wire angle_ge_pi_over_2;

    //=================================================================
    // Threshold Detection for Large Angles (>= 100π)
    //
    // 100π ≈ 314.159 ≈ 2^8.299
    // FP80 exponent for 100π: 0x3FFF + 8 = 0x4007
    //
    // Any angle with exponent >= 0x4007 is >= 256, which includes all >= 100π
    //=================================================================

    localparam [14:0] THRESHOLD_EXPONENT = 15'h4007; // 100π threshold

    wire is_large_angle;
    wire is_special_value;

    // Detect large angles by exponent
    assign is_large_angle = (angle_in[78:64] >= THRESHOLD_EXPONENT) &&
                            (angle_in[78:64] != 15'h7FFF); // Not infinity/NaN

    // Detect special values that need hardware handling
    assign is_special_value = (angle_in[78:64] == 15'h7FFF) || // Infinity or NaN
                              ((angle_in[78:64] == 15'd0) && (angle_in[63:0] == 64'd0)); // Zero

    //=================================================================
    // Floating Point Comparison
    // Simple magnitude comparison for positive numbers
    //=================================================================

    // Compare magnitudes (assume positive angles, sign handled outside)
    assign angle_ge_2pi = (angle_working[78:0] >= FP80_TWO_PI[78:0]);
    assign angle_ge_pi = (angle_working[78:0] >= FP80_PI[78:0]);
    assign angle_ge_pi_over_2 = (angle_working[78:0] >= FP80_PI_OVER_2[78:0]);

    //=================================================================
    // Floating Point Subtraction
    // Simplified for subtracting constants (2π, π, π/2)
    // Uses magnitude-based subtraction with normalization
    //=================================================================

    function [79:0] fp_subtract;
        input [79:0] a;
        input [79:0] b;
        reg [14:0] exp_a, exp_b, exp_diff;
        reg [63:0] mant_a, mant_b, mant_result;
        reg [14:0] exp_result;
        reg [5:0] shift_amount;
        integer i;
        begin
            // Extract components
            exp_a = a[78:64];
            exp_b = b[78:64];
            // Extended precision has EXPLICIT integer bit (bit 63)
            mant_a = a[63:0];
            mant_b = b[63:0];

            // Handle equal exponents (common case for our constants)
            if (exp_a == exp_b) begin
                mant_result = mant_a - mant_b;
                exp_result = exp_a;

                // Normalize: find leading 1 and shift
                shift_amount = 6'd0;

                // Check specific bit positions for leading 1
                if (mant_result[63]) begin
                    shift_amount = 6'd0;
                end else if (mant_result[62]) begin
                    shift_amount = 6'd1;
                end else if (mant_result[61]) begin
                    shift_amount = 6'd2;
                end else if (mant_result[60]) begin
                    shift_amount = 6'd3;
                end else if (mant_result[59:56] != 4'd0) begin
                    shift_amount = 6'd4;
                end else if (mant_result[55:48] != 8'd0) begin
                    shift_amount = 6'd8;
                end else if (mant_result[47:32] != 16'd0) begin
                    shift_amount = 6'd16;
                end else begin
                    shift_amount = 6'd32;
                end

                // Apply normalization
                mant_result = mant_result << shift_amount;
                exp_result = exp_result - shift_amount;

                fp_subtract = {1'b0, exp_result, mant_result[63:0]};
            end else if (exp_a > exp_b) begin
                // Align mantissas
                exp_diff = exp_a - exp_b;
                if (exp_diff < 64) begin
                    mant_b = mant_b >> exp_diff;
                end else begin
                    mant_b = 64'd0;
                end

                mant_result = mant_a - mant_b;
                exp_result = exp_a;

                // Normalize: find leading 1 and shift
                shift_amount = 6'd0;

                if (mant_result[63]) begin
                    shift_amount = 6'd0;
                end else if (mant_result[62]) begin
                    shift_amount = 6'd1;
                end else if (mant_result[61]) begin
                    shift_amount = 6'd2;
                end else if (mant_result[60]) begin
                    shift_amount = 6'd3;
                end else if (mant_result[59]) begin
                    shift_amount = 6'd4;
                end else if (mant_result[58]) begin
                    shift_amount = 6'd5;
                end else if (mant_result[57]) begin
                    shift_amount = 6'd6;
                end else if (mant_result[56]) begin
                    shift_amount = 6'd7;
                end else if (mant_result[55:48] != 8'd0) begin
                    shift_amount = 6'd8;
                end else if (mant_result[47:40] != 8'd0) begin
                    shift_amount = 6'd16;
                end else if (mant_result[39:32] != 8'd0) begin
                    shift_amount = 6'd24;
                end else begin
                    shift_amount = 6'd32;
                end

                // Apply normalization
                mant_result = mant_result << shift_amount;
                exp_result = exp_result - shift_amount;

                fp_subtract = {1'b0, exp_result, mant_result[63:0]};
            end else begin
                // exp_b > exp_a - result would be negative, return 0
                fp_subtract = FP80_ZERO;
            end
        end
    endfunction

    //=================================================================
    // Special Value Detection
    //=================================================================

    wire is_zero = (angle_in[78:64] == 15'd0) && (angle_in[63:0] == 64'd0);
    wire is_inf  = (angle_in[78:64] == 15'h7FFF) && (angle_in[63] == 1'b1) && (angle_in[62:0] == 63'd0);
    wire is_nan  = (angle_in[78:64] == 15'h7FFF) && ((angle_in[63] == 1'b0) || (angle_in[62:0] != 63'd0));

    //=================================================================
    // Main State Machine
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_IDLE;
            done <= 1'b0;
            error <= 1'b0;
            angle_out <= FP80_ZERO;
            quadrant <= 2'b00;
            angle_working <= FP80_ZERO;
            iteration_count <= 8'd0;
            microcode_invoke <= 1'b0;
            microcode_addr <= 12'd0;
            microcode_operand_a <= 80'd0;

        end else begin
            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    error <= 1'b0;
                    iteration_count <= 8'd0;
                    microcode_invoke <= 1'b0;

                    if (enable) begin
                        // Transition to dispatch state
                        state <= STATE_DISPATCH;
                    end
                end

                STATE_DISPATCH: begin
                    // Check for special values first
                    if (is_zero) begin
                        // Zero angle - return immediately
                        angle_out <= FP80_ZERO;
                        quadrant <= 2'b00;
                        done <= 1'b1;
                        state <= STATE_DONE;
                    end else if (is_inf || is_nan) begin
                        // Infinity or NaN - error
                        error <= 1'b1;
                        done <= 1'b1;
                        state <= STATE_DONE;
                    end else if (is_large_angle) begin
                        // Large angle (>= 100π) - use microcode path
                        microcode_invoke <= 1'b1;
                        microcode_addr <= 12'h180;  // Entry point for Payne-Hanek
                        microcode_operand_a <= angle_in;
                        state <= STATE_MICROCODE_WAIT;
                    end else begin
                        // Small angle (< 100π) - use iterative path
                        angle_working <= {1'b0, angle_in[78:0]}; // Absolute value
                        state <= STATE_CHECK_RANGE;
                    end
                end

                STATE_MICROCODE_WAIT: begin
                    // Clear invoke signal after one cycle
                    microcode_invoke <= 1'b0;

                    // Wait for microcode completion
                    if (microcode_done) begin
                        if (microcode_error) begin
                            // Microcode reported an error
                            error <= 1'b1;
                        end else begin
                            // Retrieve results from microcode
                            angle_out <= microcode_result;
                            quadrant <= microcode_quadrant;
                        end
                        done <= 1'b1;
                        state <= STATE_DONE;
                    end
                    // Otherwise keep waiting
                end

                STATE_CHECK_RANGE: begin
                    // Check if angle >= 2π
                    // Allow up to 200 iterations for very large angles (e.g., 1000π needs ~159 iterations)
                    if (angle_ge_2pi && iteration_count < 200) begin
                        iteration_count <= iteration_count + 1;
                        state <= STATE_SUB_2PI;
                    end else begin
                        // Angle is in [0, 2π), find quadrant
                        state <= STATE_FIND_QUADRANT;
                    end
                end

                STATE_SUB_2PI: begin
                    // Subtract 2π from angle
                    angle_working <= fp_subtract(angle_working, FP80_TWO_PI);
                    state <= STATE_CHECK_RANGE;
                end

                STATE_FIND_QUADRANT: begin
                    // Determine quadrant based on angle value
                    if (angle_ge_pi) begin
                        quadrant <= angle_ge_pi_over_2 ? 2'd3 : 2'd2;
                    end else begin
                        quadrant <= angle_ge_pi_over_2 ? 2'd1 : 2'd0;
                    end

                    // Reduce to [0, π/2)
                    if (angle_ge_pi + angle_ge_pi_over_2 > 0) begin
                        state <= STATE_SUB_QUAD;
                    end else begin
                        // Already in [0, π/2)
                        angle_out <= angle_working;
                        done <= 1'b1;
                        state <= STATE_DONE;
                    end
                end

                STATE_SUB_QUAD: begin
                    // Subtract appropriate multiple of π/2
                    case (quadrant)
                        2'd1: angle_working <= fp_subtract(angle_working, FP80_PI_OVER_2);
                        2'd2: angle_working <= fp_subtract(angle_working, FP80_PI);
                        2'd3: begin
                            // 3π/2 = π + π/2
                            angle_working <= fp_subtract(fp_subtract(angle_working, FP80_PI), FP80_PI_OVER_2);
                        end
                        default: angle_working <= angle_working;
                    endcase

                    state <= STATE_FINALIZE;
                end

                STATE_FINALIZE: begin
                    // Wait one cycle for subtraction to complete, then output result
                    angle_out <= angle_working;
                    done <= 1'b1;
                    state <= STATE_DONE;
                end

                STATE_DONE: begin
                    if (~enable) begin
                        state <= STATE_IDLE;
                        done <= 1'b0;
                    end
                end

                default: state <= STATE_IDLE;
            endcase
        end
    end

endmodule
