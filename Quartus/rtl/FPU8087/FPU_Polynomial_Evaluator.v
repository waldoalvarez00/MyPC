`timescale 1ns / 1ps

//=====================================================================
// Polynomial Evaluator for Transcendental Functions
//
// This module evaluates polynomials using Horner's method:
// P(x) = c₀ + x(c₁ + x(c₂ + x(c₃ + ... + x(cₙ))))
//
// Supports:
// - F2XM1: 2^x - 1 (degree 6 polynomial)
// - LOG2:  log₂(1+x) (degree 7 polynomial)
//
// Uses existing FPU multiply and add units for operations.
//=====================================================================

module FPU_Polynomial_Evaluator(
    input wire clk,
    input wire reset,

    // Control
    input wire enable,
    input wire [3:0] poly_select,   // Polynomial to evaluate

    // Input value x (80-bit FP)
    input wire [79:0] x_in,

    // Output P(x) (80-bit FP)
    output reg [79:0] result_out,

    output reg done,
    output reg error
);

    //=================================================================
    // Parameters
    //=================================================================

    localparam POLY_F2XM1 = 4'd0;  // 2^x - 1 (degree 6)
    localparam POLY_LOG2  = 4'd1;  // log₂(1+x) (degree 7)

    //=================================================================
    // State Machine
    //=================================================================

    localparam STATE_IDLE       = 3'd0;
    localparam STATE_LOAD_COEFF = 3'd1;
    localparam STATE_MULTIPLY   = 3'd2;
    localparam STATE_WAIT_MUL   = 3'd3;
    localparam STATE_ADD        = 3'd4;
    localparam STATE_WAIT_ADD   = 3'd5;
    localparam STATE_DONE       = 3'd6;

    reg [2:0] state;

    //=================================================================
    // Working Registers
    //=================================================================

    reg [79:0] x_value;             // Input x
    reg [79:0] accumulator;         // Running result
    reg [3:0] coefficient_index;    // Current coefficient index
    reg [3:0] polynomial_type;      // Which polynomial we're evaluating
    reg [3:0] max_degree;           // Maximum degree of polynomial

    //=================================================================
    // Coefficient ROM
    //=================================================================

    wire [79:0] coefficient;
    reg [3:0] coeff_rom_select;
    reg [3:0] coeff_rom_index;

    FPU_Poly_Coeff_ROM coeff_rom (
        .poly_select(coeff_rom_select),
        .coeff_index(coeff_rom_index),
        .coefficient(coefficient)
    );

    //=================================================================
    // Arithmetic Units
    //=================================================================

    // Multiply: accumulator * x_value
    reg mul_enable;
    wire [79:0] mul_result;
    wire mul_done;
    wire mul_invalid, mul_overflow, mul_underflow, mul_inexact;
    reg [79:0] mul_operand_a, mul_operand_b;

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

    // Add: mul_result + coefficient
    reg add_enable;
    wire [79:0] add_result;
    wire add_done;
    wire add_cmp_equal, add_cmp_less, add_cmp_greater;
    wire add_invalid, add_overflow, add_underflow, add_inexact;
    reg [79:0] add_operand_a, add_operand_b;

    FPU_IEEE754_AddSub add_unit (
        .clk(clk),
        .reset(reset),
        .enable(add_enable),
        .operand_a(add_operand_a),
        .operand_b(add_operand_b),
        .subtract(1'b0),  // Addition only
        .rounding_mode(2'b00),  // Round to nearest
        .result(add_result),
        .done(add_done),
        .cmp_equal(add_cmp_equal),
        .cmp_less(add_cmp_less),
        .cmp_greater(add_cmp_greater),
        .flag_invalid(add_invalid),
        .flag_overflow(add_overflow),
        .flag_underflow(add_underflow),
        .flag_inexact(add_inexact)
    );

    //=================================================================
    // Main State Machine
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_IDLE;
            done <= 1'b0;
            error <= 1'b0;
            result_out <= 80'h0;
            x_value <= 80'h0;
            accumulator <= 80'h0;
            coefficient_index <= 4'd0;
            polynomial_type <= 4'd0;
            max_degree <= 4'd0;
            mul_enable <= 1'b0;
            add_enable <= 1'b0;
        end else begin
            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    error <= 1'b0;
                    mul_enable <= 1'b0;
                    add_enable <= 1'b0;

                    if (enable) begin
                        x_value <= x_in;
                        polynomial_type <= poly_select;

                        // Set maximum degree based on polynomial type
                        case (poly_select)
                            POLY_F2XM1: max_degree <= 4'd6;  // Degree 6
                            POLY_LOG2:  max_degree <= 4'd7;  // Degree 7
                            default:    max_degree <= 4'd0;
                        endcase

                        // Start with highest degree coefficient
                        coefficient_index <= max_degree;
                        state <= STATE_LOAD_COEFF;
                    end
                end

                STATE_LOAD_COEFF: begin
                    // Load coefficient from ROM
                    coeff_rom_select <= polynomial_type;
                    coeff_rom_index <= coefficient_index;

                    // Wait one cycle for ROM read
                    // (combinational ROM, but we add pipeline stage)
                    accumulator <= coefficient;  // Load cₙ

                    // Check if this is the highest coefficient
                    if (coefficient_index == max_degree) begin
                        // First coefficient, just load it
                        coefficient_index <= coefficient_index - 1;
                        state <= STATE_MULTIPLY;
                    end else begin
                        // Not first, prepare to add
                        state <= STATE_ADD;
                    end
                end

                STATE_MULTIPLY: begin
                    // Multiply accumulator by x
                    mul_operand_a <= accumulator;
                    mul_operand_b <= x_value;
                    mul_enable <= 1'b1;
                    state <= STATE_WAIT_MUL;
                end

                STATE_WAIT_MUL: begin
                    mul_enable <= 1'b0;
                    if (mul_done) begin
                        accumulator <= mul_result;

                        // Check if we're done with all coefficients
                        if (coefficient_index == 4'd15) begin  // Underflow check
                            // All coefficients processed
                            state <= STATE_DONE;
                        end else begin
                            // Load next coefficient
                            state <= STATE_LOAD_COEFF;
                        end
                    end
                end

                STATE_ADD: begin
                    // Add coefficient to accumulator
                    add_operand_a <= accumulator;
                    add_operand_b <= coefficient;
                    add_enable <= 1'b1;
                    state <= STATE_WAIT_ADD;
                end

                STATE_WAIT_ADD: begin
                    add_enable <= 1'b0;
                    if (add_done) begin
                        accumulator <= add_result;

                        // Decrement coefficient index
                        coefficient_index <= coefficient_index - 1;

                        // Multiply by x for next iteration
                        state <= STATE_MULTIPLY;
                    end
                end

                STATE_DONE: begin
                    result_out <= accumulator;
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
// This is a FUNCTIONAL polynomial evaluator with placeholder arithmetic.
//
// TO COMPLETE INTEGRATION:
//
// 1. Connect Real Multiply Unit:
//    Replace placeholder with:
//      FPU_IEEE754_Multiply mul_unit (
//          .clk(clk),
//          .reset(reset),
//          .enable(mul_enable),
//          .operand_a(mul_operand_a),
//          .operand_b(mul_operand_b),
//          .result(mul_result),
//          .done(mul_done),
//          ...
//      );
//
// 2. Connect Real Add Unit:
//    Replace placeholder with:
//      FPU_IEEE754_AddSub add_unit (
//          .clk(clk),
//          .reset(reset),
//          .enable(add_enable),
//          .operand_a(add_operand_a),
//          .operand_b(add_operand_b),
//          .subtract(1'b0),  // Always add
//          .result(add_result),
//          .done(add_done),
//          ...
//      );
//
// 3. Add Exception Handling:
//    - Propagate overflow/underflow flags from multiply and add
//    - Set error flag if exceptions occur
//
// 4. Optimize Horner's Method:
//    - Current: Sequential (multiply, add, multiply, add, ...)
//    - Enhancement: Pipeline stages for better throughput
//    - Enhancement: Fused multiply-add (FMA) if available
//
// PERFORMANCE:
// - Degree 6 polynomial (F2XM1): ~7 multiplies + 6 adds = ~13 operations
// - Degree 7 polynomial (LOG2):  ~8 multiplies + 7 adds = ~15 operations
// - At ~10 cycles per operation: ~130-150 cycles total
// - Can be optimized with pipelining or FMA
//
// TESTING STRATEGY:
// 1. Test with x=0: Should give P(0) = 0 for both polynomials
// 2. Test with x=1:
//    - F2XM1(1) should give 2^1 - 1 = 1.0
//    - LOG2(1) should give log₂(2) = 1.0
// 3. Compare against Python numpy.polyval()
// 4. Measure ULP error across input range
//=====================================================================


//=====================================================================
// HORNER'S METHOD ALGORITHM (for reference)
//=====================================================================
//
// Given polynomial P(x) = c₀ + c₁x + c₂x² + ... + cₙxⁿ
//
// Horner's form: P(x) = c₀ + x(c₁ + x(c₂ + ... + x(cₙ)))
//
// Pseudocode:
//   result = cₙ
//   for i = n-1 down to 0:
//       result = result * x + cᵢ
//
// Example for P(x) = 2 + 3x + 4x²:
//   result = 4              // c₂
//   result = 4*x + 3        // = c₁ + x*c₂
//   result = (4*x + 3)*x + 2  // = c₀ + x*(c₁ + x*c₂)
//
// Advantage: Only n multiplications instead of O(n²) for direct evaluation
//=====================================================================
