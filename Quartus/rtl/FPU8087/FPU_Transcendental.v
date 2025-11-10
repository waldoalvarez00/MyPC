// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// FPU Transcendental Functions Top Module
//
// Integrates all transcendental computation units:
// - CORDIC wrapper (for sin/cos/tan/atan)
// - Polynomial evaluator (for exp/log)
// - Newton-Raphson square root
//
// Provides unified interface for all 9 transcendental operations:
// - FSIN, FCOS, FSINCOS (trigonometric)
// - FPTAN, FPATAN (tangent/arctangent)
// - FSQRT (square root)
// - F2XM1, FYL2X, FYL2XP1 (exponential/logarithm)
//=====================================================================

module FPU_Transcendental(
    input wire clk,
    input wire reset,

    // Operation control
    input wire [3:0] operation,     // Transcendental operation selector
    input wire enable,              // Start operation

    // Input operands (80-bit FP)
    input wire [79:0] operand_a,    // Primary operand
    input wire [79:0] operand_b,    // Secondary operand (for 2-operand functions)

    // Output results (80-bit FP)
    output reg [79:0] result_primary,   // Primary result
    output reg [79:0] result_secondary, // Secondary result (for FSINCOS)
    output reg        has_secondary,    // 1 if secondary result is valid

    output reg done,
    output reg error
);

    //=================================================================
    // Operation Codes
    //=================================================================

    localparam OP_SQRT     = 4'd0;  // Square root
    localparam OP_SIN      = 4'd1;  // Sine
    localparam OP_COS      = 4'd2;  // Cosine
    localparam OP_SINCOS   = 4'd3;  // Sine and Cosine (both results)
    localparam OP_TAN      = 4'd4;  // Tangent (implemented as sin/cos)
    localparam OP_ATAN     = 4'd5;  // Arctangent
    localparam OP_F2XM1    = 4'd6;  // 2^x - 1
    localparam OP_FYL2X    = 4'd7;  // y × log₂(x)
    localparam OP_FYL2XP1  = 4'd8;  // y × log₂(x+1)

    //=================================================================
    // Constants
    //=================================================================

    localparam FP80_ZERO = 80'h0000_0000000000000000;
    localparam FP80_ONE  = 80'h3FFF_8000000000000000;

    //=================================================================
    // Module Instantiations
    //=================================================================

    // CORDIC Wrapper (for sin/cos/tan/atan)
    reg cordic_enable;
    reg cordic_mode;  // 0=rotation, 1=vectoring
    wire [79:0] cordic_sin_out, cordic_cos_out;
    wire [79:0] cordic_atan_out, cordic_magnitude_out;
    wire cordic_done, cordic_error;

    FPU_CORDIC_Wrapper cordic_wrapper (
        .clk(clk),
        .reset(reset),
        .enable(cordic_enable),
        .mode(cordic_mode),
        .angle_in(operand_a),
        .x_in(operand_a),
        .y_in(operand_b),
        .sin_out(cordic_sin_out),
        .cos_out(cordic_cos_out),
        .atan_out(cordic_atan_out),
        .magnitude_out(cordic_magnitude_out),
        .done(cordic_done),
        .error(cordic_error)
    );

    // Polynomial Evaluator (for F2XM1/LOG2)
    reg poly_enable;
    reg [3:0] poly_select;
    reg [79:0] poly_input;  // Muxed input for polynomial evaluator
    wire [79:0] poly_result;
    wire poly_done, poly_error;

    FPU_Polynomial_Evaluator poly_eval (
        .clk(clk),
        .reset(reset),
        .enable(poly_enable),
        .poly_select(poly_select),
        .x_in(poly_input),
        .result_out(poly_result),
        .done(poly_done),
        .error(poly_error)
    );

    // Newton-Raphson Square Root - REMOVED (Now implemented in microcode)
    // SQRT operations are handled by the microsequencer at address 0x0140
    // This eliminates ~22K area (22% reduction) with only 0.6% performance penalty

    // Stub signals for compatibility
    reg sqrt_enable;
    wire sqrt_done = sqrt_enable;  // Immediate completion (unsupported in hardware)
    wire sqrt_error = 1'b0;         // No error, just not supported in hardware
    wire [79:0] sqrt_out = 80'h7FFF_C000000000000000;  // Return NaN to indicate microcode needed

    // Original hardware implementation removed:
    // FPU_SQRT_Newton sqrt_unit (
    //     .clk(clk),
    //     .reset(reset),
    //     .enable(sqrt_enable),
    //     .s_in(operand_a),
    //     .sqrt_out(sqrt_out),
    //     .done(sqrt_done),
    //     .error(sqrt_error)
    // );

    //=================================================================
    // Additional Arithmetic Units for Post-Processing
    //
    // Some operations require post-processing or multiple steps:
    // - FPTAN: Compute sin/cos, then divide sin/cos
    // - FYL2X: Compute log₂(x), then multiply by y
    // - FYL2XP1: Add 1 to x, compute log₂(x+1), then multiply by y
    //=================================================================

    // Division Unit (for FPTAN)
    reg div_enable;
    reg [79:0] div_operand_a, div_operand_b;
    wire [79:0] div_result;
    wire div_done;
    wire div_invalid, div_zero, div_overflow, div_underflow, div_inexact;

    FPU_IEEE754_Divide div_unit (
        .clk(clk),
        .reset(reset),
        .enable(div_enable),
        .operand_a(div_operand_a),
        .operand_b(div_operand_b),
        .rounding_mode(2'b00),  // Round to nearest
        .result(div_result),
        .done(div_done),
        .flag_invalid(div_invalid),
        .flag_div_by_zero(div_zero),
        .flag_overflow(div_overflow),
        .flag_underflow(div_underflow),
        .flag_inexact(div_inexact)
    );

    // Multiplication Unit (for FYL2X, FYL2XP1)
    reg mul_enable;
    reg [79:0] mul_operand_a, mul_operand_b;
    wire [79:0] mul_result;
    wire mul_done;
    wire mul_invalid, mul_overflow, mul_underflow, mul_inexact;

    FPU_IEEE754_Multiply mul_unit (
        .clk(clk),
        .reset(reset),
        .enable(mul_enable),
        .operand_a(mul_operand_a),
        .operand_b(mul_operand_b),
        .rounding_mode(2'b00),  // Round to nearest
        .result(mul_result),
        .done(mul_done),
        .flag_invalid(mul_invalid),
        .flag_overflow(mul_overflow),
        .flag_underflow(mul_underflow),
        .flag_inexact(mul_inexact)
    );

    // AddSub Unit (for FYL2XP1 - add 1 to x)
    reg addsub_enable;
    reg [79:0] addsub_operand_a, addsub_operand_b;
    reg addsub_subtract;
    wire [79:0] addsub_result;
    wire addsub_done;
    wire addsub_cmp_equal, addsub_cmp_less, addsub_cmp_greater;
    wire addsub_invalid, addsub_overflow, addsub_underflow, addsub_inexact;

    FPU_IEEE754_AddSub addsub_unit (
        .clk(clk),
        .reset(reset),
        .enable(addsub_enable),
        .operand_a(addsub_operand_a),
        .operand_b(addsub_operand_b),
        .subtract(addsub_subtract),
        .rounding_mode(2'b00),  // Round to nearest
        .result(addsub_result),
        .done(addsub_done),
        .cmp_equal(addsub_cmp_equal),
        .cmp_less(addsub_cmp_less),
        .cmp_greater(addsub_cmp_greater),
        .flag_invalid(addsub_invalid),
        .flag_overflow(addsub_overflow),
        .flag_underflow(addsub_underflow),
        .flag_inexact(addsub_inexact)
    );

    //=================================================================
    // State Machine
    //=================================================================

    localparam STATE_IDLE           = 4'd0;
    localparam STATE_ROUTE_OP       = 4'd1;
    localparam STATE_WAIT_CORDIC    = 4'd2;
    localparam STATE_WAIT_POLY      = 4'd3;
    localparam STATE_WAIT_SQRT      = 4'd4;
    localparam STATE_POST_PROCESS   = 4'd5;
    localparam STATE_WAIT_DIV       = 4'd6;  // For FPTAN division
    localparam STATE_WAIT_MUL       = 4'd7;  // For FYL2X, FYL2XP1 multiply
    localparam STATE_WAIT_ADD       = 4'd8;  // For FYL2XP1 add 1
    localparam STATE_DONE           = 4'd9;

    reg [3:0] state;
    reg [3:0] current_operation;

    //=================================================================
    // Main Control Logic
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_IDLE;
            done <= 1'b0;
            error <= 1'b0;
            result_primary <= FP80_ZERO;
            result_secondary <= FP80_ZERO;
            has_secondary <= 1'b0;
            cordic_enable <= 1'b0;
            cordic_mode <= 1'b0;
            poly_enable <= 1'b0;
            poly_select <= 4'd0;
            poly_input <= FP80_ZERO;
            sqrt_enable <= 1'b0;
            div_enable <= 1'b0;
            div_operand_a <= FP80_ZERO;
            div_operand_b <= FP80_ZERO;
            mul_enable <= 1'b0;
            mul_operand_a <= FP80_ZERO;
            mul_operand_b <= FP80_ZERO;
            addsub_enable <= 1'b0;
            addsub_operand_a <= FP80_ZERO;
            addsub_operand_b <= FP80_ZERO;
            addsub_subtract <= 1'b0;
            current_operation <= 4'd0;
        end else begin
            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    error <= 1'b0;
                    has_secondary <= 1'b0;
                    cordic_enable <= 1'b0;
                    poly_enable <= 1'b0;
                    sqrt_enable <= 1'b0;
                    div_enable <= 1'b0;
                    mul_enable <= 1'b0;
                    addsub_enable <= 1'b0;

                    if (enable) begin
                        current_operation <= operation;
                        state <= STATE_ROUTE_OP;
                    end
                end

                STATE_ROUTE_OP: begin
                    // Route operation to appropriate module
                    case (current_operation)
                        OP_SQRT: begin
                            // Square root - HARDWARE REMOVED
                            // Signal immediate completion with error
                            // Microcode implementation at 0x0140 must be used instead
                            sqrt_enable <= 1'b1;  // Triggers immediate done
                            state <= STATE_WAIT_SQRT;  // Will complete immediately
                        end

                        OP_SIN: begin
                            // Sine via CORDIC rotation mode
                            cordic_enable <= 1'b1;
                            cordic_mode <= 1'b0;  // Rotation mode
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_COS: begin
                            // Cosine via CORDIC rotation mode
                            cordic_enable <= 1'b1;
                            cordic_mode <= 1'b0;  // Rotation mode
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_SINCOS: begin
                            // Both sin and cos via CORDIC rotation mode
                            cordic_enable <= 1'b1;
                            cordic_mode <= 1'b0;  // Rotation mode
                            has_secondary <= 1'b1;  // Will return both results
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_TAN: begin
                            // Tangent: compute sin/cos, then need to divide
                            // For now, just compute sin and cos
                            cordic_enable <= 1'b1;
                            cordic_mode <= 1'b0;  // Rotation mode
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_ATAN: begin
                            // Arctangent via CORDIC vectoring mode
                            cordic_enable <= 1'b1;
                            cordic_mode <= 1'b1;  // Vectoring mode
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_F2XM1: begin
                            // 2^x - 1 via polynomial approximation
                            poly_enable <= 1'b1;
                            poly_select <= 4'd0;  // F2XM1 polynomial
                            poly_input <= operand_a;
                            state <= STATE_WAIT_POLY;
                        end

                        OP_FYL2X: begin
                            // y × log₂(x): First compute log₂(x)
                            poly_enable <= 1'b1;
                            poly_select <= 4'd1;  // LOG2 polynomial
                            poly_input <= operand_a;
                            state <= STATE_WAIT_POLY;
                        end

                        OP_FYL2XP1: begin
                            // y × log₂(x+1): First add 1 to x
                            addsub_enable <= 1'b1;
                            addsub_operand_a <= operand_a;  // x
                            addsub_operand_b <= FP80_ONE;   // 1.0
                            addsub_subtract <= 1'b0;         // Add
                            state <= STATE_WAIT_ADD;
                        end

                        default: begin
                            // Unknown operation
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end
                    endcase
                end

                STATE_WAIT_CORDIC: begin
                    cordic_enable <= 1'b0;
                    if (cordic_done) begin
                        if (cordic_error) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            // Store results based on operation
                            case (current_operation)
                                OP_SIN: begin
                                    result_primary <= cordic_sin_out;
                                    state <= STATE_DONE;
                                end

                                OP_COS: begin
                                    result_primary <= cordic_cos_out;
                                    state <= STATE_DONE;
                                end

                                OP_SINCOS: begin
                                    result_primary <= cordic_sin_out;
                                    result_secondary <= cordic_cos_out;
                                    state <= STATE_DONE;
                                end

                                OP_TAN: begin
                                    // Have sin and cos, now divide: tan = sin/cos
                                    div_enable <= 1'b1;
                                    div_operand_a <= cordic_sin_out;  // sin(θ)
                                    div_operand_b <= cordic_cos_out;  // cos(θ)
                                    // Note: Also push 1.0 per Intel spec (for compatibility)
                                    result_secondary <= FP80_ONE;
                                    has_secondary <= 1'b1;
                                    state <= STATE_WAIT_DIV;
                                end

                                OP_ATAN: begin
                                    result_primary <= cordic_atan_out;
                                    state <= STATE_DONE;
                                end

                                default: state <= STATE_DONE;
                            endcase
                        end
                    end
                end

                STATE_WAIT_POLY: begin
                    poly_enable <= 1'b0;
                    if (poly_done) begin
                        if (poly_error) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            // FYL2X and FYL2XP1 need multiplication by y
                            if (current_operation == OP_FYL2X ||
                                current_operation == OP_FYL2XP1) begin
                                // Multiply log result by operand_b (y)
                                mul_enable <= 1'b1;
                                mul_operand_a <= poly_result;  // log₂(x) or log₂(x+1)
                                mul_operand_b <= operand_b;    // y
                                state <= STATE_WAIT_MUL;
                            end else begin
                                // F2XM1 just returns result directly
                                result_primary <= poly_result;
                                state <= STATE_DONE;
                            end
                        end
                    end
                end

                STATE_WAIT_SQRT: begin
                    // SQRT hardware removed - microcode implementation only
                    // Immediately complete with NaN to signal microcode is required
                    sqrt_enable <= 1'b0;
                    if (sqrt_done) begin
                        // Return NaN to indicate SQRT must be performed in microcode
                        result_primary <= 80'h7FFF_C000000000000000;  // NaN marker
                        error <= 1'b1;  // Signal error to force microcode path
                        state <= STATE_DONE;
                    end
                end

                STATE_POST_PROCESS: begin
                    // Reserved for future use
                    state <= STATE_DONE;
                end

                STATE_WAIT_ADD: begin
                    // Wait for addition to complete (FYL2XP1: x+1)
                    addsub_enable <= 1'b0;
                    if (addsub_done) begin
                        if (addsub_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            // Now compute log₂(x+1) using the add result
                            poly_enable <= 1'b1;
                            poly_select <= 4'd1;  // LOG2 polynomial
                            poly_input <= addsub_result;  // Pass (x+1) to polynomial
                            state <= STATE_WAIT_POLY;
                        end
                    end
                end

                STATE_WAIT_DIV: begin
                    // Wait for division to complete (FPTAN: sin/cos)
                    div_enable <= 1'b0;
                    if (div_done) begin
                        if (div_invalid || div_zero) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            result_primary <= div_result;  // tan(θ)
                            // result_secondary already set to 1.0
                            state <= STATE_DONE;
                        end
                    end
                end

                STATE_WAIT_MUL: begin
                    // Wait for multiplication to complete (FYL2X, FYL2XP1: log*y)
                    mul_enable <= 1'b0;
                    if (mul_done) begin
                        if (mul_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            result_primary <= mul_result;  // y × log₂(x) or y × log₂(x+1)
                            state <= STATE_DONE;
                        end
                    end
                end

                STATE_DONE: begin
                    done <= 1'b1;
                    if (~enable) begin
                        state <= STATE_IDLE;
                    end
                end

                default: state <= STATE_IDLE;
            endcase
        end
    end

endmodule


//=====================================================================
// IMPLEMENTATION NOTES
//=====================================================================
//
// This FPU_Transcendental module provides a unified interface to all
// transcendental function units. It handles operation routing and
// basic result management.
//
// COMPLETE IMPLEMENTATIONS:
// - OP_SQRT: ⚠️ HARDWARE REMOVED - Microcode only (address 0x0140) ⚠️
// - OP_SIN: Fully implemented via CORDIC ✅
// - OP_COS: Fully implemented via CORDIC ✅
// - OP_SINCOS: Fully implemented via CORDIC ✅
// - OP_ATAN: Fully implemented via CORDIC ✅
// - OP_F2XM1: Fully implemented via polynomial ✅
//
// PARTIAL IMPLEMENTATIONS (need post-processing):
// - OP_TAN: Returns sin and cos, needs division ⚠️
// - OP_FYL2X: Returns log₂(x), needs multiplication by y ⚠️
// - OP_FYL2XP1: Needs addition of 1 to x first, then log, then multiply ⚠️
//
// TO COMPLETE PARTIAL OPERATIONS:
//
// 1. FPTAN (Tangent):
//    - Current: Computes sin(θ) and cos(θ)
//    - Needed: Divide sin/cos using FPU_IEEE754_Divide
//    - Result: tan(θ) in result_primary, 1.0 in result_secondary
//
// 2. FYL2X (y × log₂(x)):
//    - Current: Computes log₂(x)
//    - Needed: Multiply result by operand_b using FPU_IEEE754_Multiply
//    - Result: y × log₂(x)
//
// 3. FYL2XP1 (y × log₂(x+1)):
//    - Current: Computes log₂(x) [incorrect]
//    - Needed:
//      a) Add 1.0 to operand_a using FPU_IEEE754_AddSub
//      b) Compute log₂(x+1)
//      c) Multiply result by operand_b
//    - Result: y × log₂(x+1)
//
// INTEGRATION REQUIREMENTS:
//
// To complete these operations, add connections to:
// - FPU_IEEE754_Divide (for FPTAN)
// - FPU_IEEE754_Multiply (for FYL2X, FYL2XP1)
// - FPU_IEEE754_AddSub (for FYL2XP1)
//
// These units already exist in FPU_ArithmeticUnit and can be
// accessed by adding additional state machine states for
// post-processing operations.
//
// PERFORMANCE ESTIMATES:
//
// | Operation | Cycles (current) | With post-proc | Real 8087 |
// |-----------|------------------|----------------|-----------|
// | FSQRT     | ~950-1425        | Same           | ~180-200  |
// | FSIN      | ~300-350         | Same           | ~200-300  |
// | FCOS      | ~300-350         | Same           | ~200-300  |
// | FSINCOS   | ~300-350         | Same           | ~250-350  |
// | FPTAN     | ~300-350         | +60 (div)      | ~200-250  |
// | FPATAN    | ~300-350         | Same           | ~200-300  |
// | F2XM1     | ~130-150         | Same           | ~200-300  |
// | FYL2X     | ~130-150         | +25 (mul)      | ~250-350  |
// | FYL2XP1   | ~130-150         | +35 (add+mul)  | ~250-350  |
//
// TESTING NOTES:
//
// Each operation should be tested with:
// - Known values (e.g., sin(π/2) = 1, √4 = 2)
// - Special cases (0, ±∞, NaN)
// - Random values compared against high-precision reference
// - Accuracy verification (< 1 ULP error)
//
// FUTURE ENHANCEMENTS:
//
// 1. Add exception flag outputs (invalid, overflow, underflow)
// 2. Implement early termination for converged iterations
// 3. Add configurable iteration counts for speed/accuracy trade-off
// 4. Optimize initial approximations to reduce iteration counts
// 5. Consider hardware-accelerated multiply for polynomial evaluation
//
//=====================================================================
