// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// CORDIC Wrapper for FPU Transcendental Functions
//
// This module provides an 80-bit FP interface to the CORDIC engine
// for computing trigonometric functions (sin, cos, tan, atan).
//
// Modes:
// - ROTATION MODE: Compute sin/cos given angle
// - VECTORING MODE: Compute atan/magnitude given x,y coordinates
//
// The wrapper handles:
// - FP80 to fixed-point conversion
// - Range reduction (via FPU_Range_Reduction)
// - CORDIC iteration control
// - Fixed-point to FP80 conversion
// - Quadrant correction for sin/cos
//
// Precision: 50 iterations for ~64-bit mantissa accuracy
//=====================================================================

module FPU_CORDIC_Wrapper(
    input wire clk,
    input wire reset,

    // Control
    input wire enable,
    input wire [1:0] mode,      // 00=rotation (sin/cos), 01=vectoring (atan), 10=tan, 11=reserved

    // Inputs (80-bit FP)
    input wire [79:0] angle_in,     // For rotation and tan modes
    input wire [79:0] x_in,         // For vectoring mode
    input wire [79:0] y_in,         // For vectoring mode

    // Outputs (80-bit FP)
    output reg [79:0] sin_out,      // Rotation mode: sin result
    output reg [79:0] cos_out,      // Rotation mode: cos result
    output reg [79:0] atan_out,     // Vectoring mode: atan result
    output reg [79:0] magnitude_out,// Vectoring mode: magnitude result
    output reg [79:0] tan_out,      // Tan mode: tan result

    output reg done,
    output reg error,

    // External arithmetic unit interface (shared AddSub/MulDiv)
    output reg        ext_addsub_req,
    output reg [79:0] ext_addsub_a,
    output reg [79:0] ext_addsub_b,
    output reg        ext_addsub_sub,  // 0=add, 1=sub
    input wire [79:0] ext_addsub_result,
    input wire        ext_addsub_done,
    input wire        ext_addsub_invalid,

    output reg        ext_muldiv_req,
    output reg        ext_muldiv_op,   // 0=mul, 1=div
    output reg [79:0] ext_muldiv_a,
    output reg [79:0] ext_muldiv_b,
    input wire [79:0] ext_muldiv_result,
    input wire        ext_muldiv_done,
    input wire        ext_muldiv_invalid
);

    //=================================================================
    // Parameters
    //=================================================================

    localparam NUM_ITERATIONS_SINCOS = 50;  // 50 iterations for high precision sin/cos
    localparam NUM_ITERATIONS_TANATAN = 16; // 16 iterations for tan/atan + correction

    // CORDIC operation modes
    localparam MODE_ROTATION  = 2'b00;  // SIN/COS
    localparam MODE_VECTORING = 2'b01;  // ATAN
    localparam MODE_TAN       = 2'b10;  // TAN (rotation + correction)

    // CORDIC gain K ≈ 1.646760258121 (accumulated from iterations)
    // To get direct sin/cos output, start with x = 1/K ≈ 0.6072529350088812
    // In FP80 format: sign=0, exp=0x3FFE, mant=0x9B74EDA81F6EB000
    localparam FP80_CORDIC_SCALE = 80'h3FFE_9B74EDA81F6EB000;  // 1/K for pre-scaling

    // CORDIC gain for 16 iterations: K16 ≈ 1.207497
    // 1/K16 ≈ 0.828159 = FP80: 0x3FFE, 0xD413CCCFE779921B
    localparam FP80_CORDIC_SCALE_16 = 80'h3FFE_D413CCCFE779921B;  // 1/K16 for TAN/ATAN

    // Constants
    localparam FP80_ZERO = 80'h0000_0000000000000000;
    localparam FP80_ONE  = 80'h3FFF_8000000000000000;

    //=================================================================
    // Correction Constants for TAN/ATAN (Plan 2)
    //
    // For ATAN: correction = ε × (1 - ε²/3)
    // For TAN:  correction = ε × (1 + ε²/3)
    // where ε = residual angle after 16 iterations
    //=================================================================

    // Correction polynomial coefficients
    reg [79:0] correction_c1_atan;  // C1 for ATAN: 1.0
    reg [79:0] correction_c3_atan;  // C3 for ATAN: -0.333333...
    reg [79:0] correction_c1_tan;   // C1 for TAN: 1.0
    reg [79:0] correction_c3_tan;   // C3 for TAN: +0.333333...

    initial begin
        correction_c1_atan = 80'h3FFF_8000000000000000;  // 1.0
        correction_c3_atan = 80'hBFFD_AAAAAAAAAAAAAAAB;  // -1/3 ≈ -0.333333333...
        correction_c1_tan  = 80'h3FFF_8000000000000000;  // 1.0
        correction_c3_tan  = 80'h3FFD_AAAAAAAAAAAAAAAB;  // +1/3 ≈ +0.333333333...
    end

    //=================================================================
    // State Machine
    //=================================================================

    localparam STATE_IDLE           = 5'd0;
    localparam STATE_RANGE_REDUCE   = 5'd1;
    localparam STATE_CONVERT_INPUT  = 5'd2;
    localparam STATE_CORDIC_INIT    = 5'd3;
    localparam STATE_CORDIC_ITER    = 5'd4;
    localparam STATE_CONVERT_OUTPUT = 5'd5;
    localparam STATE_QUAD_CORRECT   = 5'd6;
    localparam STATE_DONE           = 5'd7;

    // Correction states for TAN/ATAN (Plan 2)
    localparam STATE_CORR_CALC_RESIDUAL  = 5'd8;   // Compute y/x for ATAN residual
    localparam STATE_CORR_WAIT_RESIDUAL  = 5'd9;   // Wait for residual division
    localparam STATE_CORR_MUL_E2         = 5'd10;  // Multiply ε × ε
    localparam STATE_CORR_WAIT_MUL_E2    = 5'd11;  // Wait for ε²
    localparam STATE_CORR_MUL_C3         = 5'd12;  // Multiply ε² × coeff
    localparam STATE_CORR_WAIT_MUL_C3    = 5'd13;  // Wait for ε² × C3
    localparam STATE_CORR_ADD_C1         = 5'd14;  // Add/sub 1 ± ε²·C3
    localparam STATE_CORR_WAIT_ADD       = 5'd15;  // Wait for 1 ± ε²·C3
    localparam STATE_CORR_MUL_E          = 5'd16;  // Multiply ε × (...)
    localparam STATE_CORR_WAIT_MUL_E     = 5'd17;  // Wait for ε × (1±ε²/3)
    localparam STATE_CORR_COMBINE        = 5'd18;  // Combine with CORDIC result
    localparam STATE_CORR_WAIT_COMBINE   = 5'd19;  // Wait for final result

    reg [4:0] state;
    reg [5:0] iteration_count;
    reg [5:0] max_iterations;  // Dynamic iteration count (50 or 16)

    //=================================================================
    // Range Reduction (for rotation mode)
    //=================================================================

    reg range_reduce_enable;
    wire [79:0] angle_reduced;
    wire [1:0] quadrant;
    wire swap_sincos, negate_sin, negate_cos;
    wire range_reduce_done, range_reduce_error;

    FPU_Range_Reduction range_reducer (
        .clk(clk),
        .reset(reset),
        .enable(range_reduce_enable),
        .angle_in(angle_in),
        .angle_out(angle_reduced),
        .quadrant(quadrant),
        .swap_sincos(swap_sincos),
        .negate_sin(negate_sin),
        .negate_cos(negate_cos),
        .done(range_reduce_done),
        .error(range_reduce_error)
    );

    //=================================================================
    // Arctangent Table
    //=================================================================

    wire [5:0] atan_index;
    wire [79:0] atan_value;

    // Connect iteration_count directly to atan table for combinational lookup
    assign atan_index = iteration_count;

    FPU_Atan_Table atan_table (
        .index(atan_index),
        .atan_value(atan_value)
    );

    //=================================================================
    // CORDIC Working Registers (64-bit fixed-point)
    //
    // Format: Q2.62 (2 integer bits, 62 fractional bits)
    // Range: [-2, +2) with resolution of 2^-62
    //=================================================================

    reg signed [63:0] x_cordic, y_cordic, z_cordic;
    reg signed [63:0] x_next, y_next, z_next;
    reg signed [63:0] x_shifted, y_shifted;
    reg signed [63:0] atan_fixed;

    //=================================================================
    // Mode and quadrant registers
    //=================================================================

    reg [1:0] cordic_mode;
    reg [1:0] result_quadrant;
    reg result_swap, result_negate_sin, result_negate_cos;

    //=================================================================
    // Correction Working Registers (for TAN/ATAN modes)
    //=================================================================

    reg [79:0] residual_angle;      // ε - residual after 16 CORDIC iterations
    reg [79:0] epsilon_squared;     // ε²
    reg [79:0] epsilon_sq_times_c3; // ε² × C3
    reg [79:0] one_plus_epsilon_term; // 1 ± ε²·C3
    reg [79:0] correction_value;    // Final correction: ε × (1 ± ε²/3)
    reg [79:0] cordic_partial_result; // Partial CORDIC result before correction

    //=================================================================
    // FP80 to Fixed-Point Conversion
    //
    // Simplified conversion for demonstration.
    // Real implementation needs full IEEE 754 unpacking.
    //=================================================================

    function signed [63:0] fp80_to_fixed;
        input [79:0] fp80_val;
        reg sign;
        reg [14:0] exponent;
        reg [63:0] mantissa;
        reg signed [63:0] result;
        integer shift_amount;
        begin
            // Initialize to prevent latch inference
            shift_amount = 0;
            result = 0;

            sign = fp80_val[79];
            exponent = fp80_val[78:64];
            mantissa = fp80_val[63:0];

            if (exponent == 15'd0) begin
                // Zero or denormal
                result = 64'd0;
            end else begin
                // Normalized value
                // FP80: value = mantissa * 2^(exp - bias - 63) [mantissa has binary point after bit 63]
                // Q2.62: value_Q = value * 2^62
                // So: value_Q = mantissa * 2^(exp - bias - 63 + 62) = mantissa * 2^(exp - bias - 1)
                shift_amount = exponent - 16384;  // exponent - bias - 1, where bias=16383

                if (shift_amount >= 0) begin
                    result = mantissa << shift_amount;
                end else begin
                    result = mantissa >>> (-shift_amount);
                end

                if (sign) result = -result;
            end

            fp80_to_fixed = result;
        end
    endfunction

    //=================================================================
    // Fixed-Point to FP80 Conversion
    //
    // Converts Q2.62 fixed-point to FP80
    //=================================================================

    function [79:0] fixed_to_fp80;
        input signed [63:0] fixed_val;
        reg sign;
        reg [14:0] exponent;
        reg [63:0] mantissa;
        reg [63:0] abs_val;
        integer leading_zeros;
        integer i;
        begin
            // Initialize to prevent latch inference
            sign = 0;
            exponent = 0;
            mantissa = 0;
            abs_val = 0;
            leading_zeros = 0;

            if (fixed_val == 64'd0) begin
                fixed_to_fp80 = FP80_ZERO;
            end else begin
                sign = fixed_val[63];
                abs_val = sign ? -fixed_val : fixed_val;

                // Find leading one position (priority encoder) - synthesis-friendly
                casez (abs_val)
                    64'b1???????????????????????????????????????????????????????????????: leading_zeros = 0;
                    64'b01??????????????????????????????????????????????????????????????: leading_zeros = 1;
                    64'b001?????????????????????????????????????????????????????????????: leading_zeros = 2;
                    64'b0001????????????????????????????????????????????????????????????: leading_zeros = 3;
                    64'b00001???????????????????????????????????????????????????????????: leading_zeros = 4;
                    64'b000001??????????????????????????????????????????????????????????: leading_zeros = 5;
                    64'b0000001?????????????????????????????????????????????????????????: leading_zeros = 6;
                    64'b00000001????????????????????????????????????????????????????????: leading_zeros = 7;
                    64'b000000001???????????????????????????????????????????????????????: leading_zeros = 8;
                    64'b0000000001??????????????????????????????????????????????????????: leading_zeros = 9;
                    64'b00000000001?????????????????????????????????????????????????????: leading_zeros = 10;
                    64'b000000000001????????????????????????????????????????????????????: leading_zeros = 11;
                    64'b0000000000001???????????????????????????????????????????????????: leading_zeros = 12;
                    64'b00000000000001??????????????????????????????????????????????????: leading_zeros = 13;
                    64'b000000000000001?????????????????????????????????????????????????: leading_zeros = 14;
                    64'b0000000000000001????????????????????????????????????????????????: leading_zeros = 15;
                    64'b00000000000000001???????????????????????????????????????????????: leading_zeros = 16;
                    64'b000000000000000001??????????????????????????????????????????????: leading_zeros = 17;
                    64'b0000000000000000001?????????????????????????????????????????????: leading_zeros = 18;
                    64'b00000000000000000001????????????????????????????????????????????: leading_zeros = 19;
                    64'b000000000000000000001???????????????????????????????????????????: leading_zeros = 20;
                    64'b0000000000000000000001??????????????????????????????????????????: leading_zeros = 21;
                    64'b00000000000000000000001?????????????????????????????????????????: leading_zeros = 22;
                    64'b000000000000000000000001????????????????????????????????????????: leading_zeros = 23;
                    64'b0000000000000000000000001???????????????????????????????????????: leading_zeros = 24;
                    64'b00000000000000000000000001??????????????????????????????????????: leading_zeros = 25;
                    64'b000000000000000000000000001?????????????????????????????????????: leading_zeros = 26;
                    64'b0000000000000000000000000001????????????????????????????????????: leading_zeros = 27;
                    64'b00000000000000000000000000001???????????????????????????????????: leading_zeros = 28;
                    64'b000000000000000000000000000001??????????????????????????????????: leading_zeros = 29;
                    64'b0000000000000000000000000000001?????????????????????????????????: leading_zeros = 30;
                    64'b00000000000000000000000000000001????????????????????????????????: leading_zeros = 31;
                    64'b000000000000000000000000000000001???????????????????????????????: leading_zeros = 32;
                    64'b0000000000000000000000000000000001??????????????????????????????: leading_zeros = 33;
                    64'b00000000000000000000000000000000001?????????????????????????????: leading_zeros = 34;
                    64'b000000000000000000000000000000000001????????????????????????????: leading_zeros = 35;
                    64'b0000000000000000000000000000000000001???????????????????????????: leading_zeros = 36;
                    64'b00000000000000000000000000000000000001??????????????????????????: leading_zeros = 37;
                    64'b000000000000000000000000000000000000001?????????????????????????: leading_zeros = 38;
                    64'b0000000000000000000000000000000000000001????????????????????????: leading_zeros = 39;
                    64'b00000000000000000000000000000000000000001???????????????????????: leading_zeros = 40;
                    64'b000000000000000000000000000000000000000001??????????????????????: leading_zeros = 41;
                    64'b0000000000000000000000000000000000000000001?????????????????????: leading_zeros = 42;
                    64'b00000000000000000000000000000000000000000001????????????????????: leading_zeros = 43;
                    64'b000000000000000000000000000000000000000000001???????????????????: leading_zeros = 44;
                    64'b0000000000000000000000000000000000000000000001??????????????????: leading_zeros = 45;
                    64'b00000000000000000000000000000000000000000000001?????????????????: leading_zeros = 46;
                    64'b000000000000000000000000000000000000000000000001????????????????: leading_zeros = 47;
                    64'b0000000000000000000000000000000000000000000000001???????????????: leading_zeros = 48;
                    64'b00000000000000000000000000000000000000000000000001??????????????: leading_zeros = 49;
                    64'b000000000000000000000000000000000000000000000000001?????????????: leading_zeros = 50;
                    64'b0000000000000000000000000000000000000000000000000001????????????: leading_zeros = 51;
                    64'b00000000000000000000000000000000000000000000000000001???????????: leading_zeros = 52;
                    64'b000000000000000000000000000000000000000000000000000001??????????: leading_zeros = 53;
                    64'b0000000000000000000000000000000000000000000000000000001?????????: leading_zeros = 54;
                    64'b00000000000000000000000000000000000000000000000000000001????????: leading_zeros = 55;
                    64'b000000000000000000000000000000000000000000000000000000001???????: leading_zeros = 56;
                    64'b0000000000000000000000000000000000000000000000000000000001??????: leading_zeros = 57;
                    64'b00000000000000000000000000000000000000000000000000000000001?????: leading_zeros = 58;
                    64'b000000000000000000000000000000000000000000000000000000000001????: leading_zeros = 59;
                    64'b0000000000000000000000000000000000000000000000000000000000001???: leading_zeros = 60;
                    64'b00000000000000000000000000000000000000000000000000000000000001??: leading_zeros = 61;
                    64'b000000000000000000000000000000000000000000000000000000000000001?: leading_zeros = 62;
                    64'b0000000000000000000000000000000000000000000000000000000000000001: leading_zeros = 63;
                    default: leading_zeros = 64; // All zeros
                endcase

                // Normalize mantissa
                mantissa = abs_val << leading_zeros;

                // Compute exponent
                // Q2.62 value represents: fixed_val / 2^62
                // FP80 mantissa has binary point after bit 63
                // FP80 value = mantissa * 2^(exp - bias - 63)
                // We want: mantissa * 2^(exp - bias - 63) = abs_val * 2^-62
                // After normalization: mantissa[63]=1, mantissa = abs_val << leading_zeros
                // So: (abs_val << leading_zeros) * 2^(exp - 16383 - 63) = abs_val * 2^-62
                // => exp - 16446 = -62 - leading_zeros
                // => exp = 16384 - leading_zeros
                exponent = 16384 - leading_zeros;

                fixed_to_fp80 = {sign, exponent, mantissa};
            end
        end
    endfunction

    //=================================================================
    // Main State Machine
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_IDLE;
            done <= 1'b0;
            error <= 1'b0;
            sin_out <= FP80_ZERO;
            cos_out <= FP80_ZERO;
            atan_out <= FP80_ZERO;
            magnitude_out <= FP80_ZERO;
            tan_out <= FP80_ZERO;
            range_reduce_enable <= 1'b0;
            iteration_count <= 6'd0;
            max_iterations <= 6'd50;
            cordic_mode <= MODE_ROTATION;
            x_cordic <= 64'd0;
            y_cordic <= 64'd0;
            z_cordic <= 64'd0;
            // Shared unit interface
            ext_addsub_req <= 1'b0;
            ext_addsub_a <= 80'd0;
            ext_addsub_b <= 80'd0;
            ext_addsub_sub <= 1'b0;
            ext_muldiv_req <= 1'b0;
            ext_muldiv_op <= 1'b0;
            ext_muldiv_a <= 80'd0;
            ext_muldiv_b <= 80'd0;
            // Correction registers
            residual_angle <= 80'd0;
            epsilon_squared <= 80'd0;
            epsilon_sq_times_c3 <= 80'd0;
            one_plus_epsilon_term <= 80'd0;
            correction_value <= 80'd0;
            cordic_partial_result <= 80'd0;
        end else begin
            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    error <= 1'b0;
                    ext_addsub_req <= 1'b0;  // Clear request signals
                    ext_muldiv_req <= 1'b0;
                    if (enable) begin
                        cordic_mode <= mode;
                        if (mode == MODE_ROTATION) begin
                            // SIN/COS mode: 50 iterations, reduce angle first
                            max_iterations <= NUM_ITERATIONS_SINCOS;
                            range_reduce_enable <= 1'b1;
                            state <= STATE_RANGE_REDUCE;
                        end else if (mode == MODE_TAN) begin
                            // TAN mode: 16 iterations + correction, reduce angle first
                            max_iterations <= NUM_ITERATIONS_TANATAN;
                            range_reduce_enable <= 1'b1;
                            state <= STATE_RANGE_REDUCE;
                        end else if (mode == MODE_VECTORING) begin
                            // ATAN mode: 16 iterations + correction, skip range reduction
                            max_iterations <= NUM_ITERATIONS_TANATAN;
                            state <= STATE_CONVERT_INPUT;
                        end else begin
                            // Invalid mode
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end
                    end
                end

                STATE_RANGE_REDUCE: begin
                    range_reduce_enable <= 1'b0;
                    if (range_reduce_done) begin
                        if (range_reduce_error) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            // Save quadrant info for later correction
                            result_quadrant <= quadrant;
                            result_swap <= swap_sincos;
                            result_negate_sin <= negate_sin;
                            result_negate_cos <= negate_cos;
                            state <= STATE_CONVERT_INPUT;
                        end
                    end
                end

                STATE_CONVERT_INPUT: begin
                    if (cordic_mode == MODE_ROTATION) begin
                        // SIN/COS mode: x = 1/K, y = 0, z = angle (50 iterations)
                        // Pre-scaling by 1/K gives direct cos(θ), sin(θ) output
                        x_cordic <= fp80_to_fixed(FP80_CORDIC_SCALE);
                        y_cordic <= 64'd0;
                        z_cordic <= fp80_to_fixed(angle_reduced);
                    end else if (cordic_mode == MODE_TAN) begin
                        // TAN mode: x = 1/K16, y = 0, z = angle (16 iterations + correction)
                        x_cordic <= fp80_to_fixed(FP80_CORDIC_SCALE_16);
                        y_cordic <= 64'd0;
                        z_cordic <= fp80_to_fixed(angle_reduced);
                    end else begin
                        // ATAN mode: x = x_in/2, y = y_in/2, z = 0 (16 iterations + correction)
                        // Pre-scale by 1/2 to prevent overflow during CORDIC iterations
                        // (First iteration can produce x+y which may exceed Q2.62 range)
                        x_cordic <= fp80_to_fixed(x_in) >>> 1;  // Divide by 2
                        y_cordic <= fp80_to_fixed(y_in) >>> 1;  // Divide by 2
                        z_cordic <= 64'd0;
                    end
                    state <= STATE_CORDIC_INIT;
                end

                STATE_CORDIC_INIT: begin
                    iteration_count <= 6'd0;
                    state <= STATE_CORDIC_ITER;
                end

                STATE_CORDIC_ITER: begin
                    // Perform one CORDIC iteration
                    // Shift amounts
                    x_shifted = x_cordic >>> iteration_count;  // Arithmetic right shift
                    y_shifted = y_cordic >>> iteration_count;

                    // Convert atan table value to fixed-point (atan_index is wired to iteration_count)
                    atan_fixed = fp80_to_fixed(atan_value);

                    // CORDIC micro-rotation
                    if (cordic_mode == MODE_ROTATION || cordic_mode == MODE_TAN) begin
                        // Rotation mode: rotate by z
                        if (z_cordic >= 0) begin
                            x_next = x_cordic - y_shifted;
                            y_next = y_cordic + x_shifted;
                            z_next = z_cordic - atan_fixed;
                        end else begin
                            x_next = x_cordic + y_shifted;
                            y_next = y_cordic - x_shifted;
                            z_next = z_cordic + atan_fixed;
                        end
                    end else begin
                        // Vectoring mode (ATAN): rotate to zero y
                        if (y_cordic < 0) begin
                            x_next = x_cordic - y_shifted;
                            y_next = y_cordic + x_shifted;
                            z_next = z_cordic - atan_fixed;
                        end else begin
                            x_next = x_cordic + y_shifted;
                            y_next = y_cordic - x_shifted;
                            z_next = z_cordic + atan_fixed;
                        end
                    end

                    // Update registers
                    x_cordic <= x_next;
                    y_cordic <= y_next;
                    z_cordic <= z_next;

                    // Check iteration count
                    if (iteration_count >= max_iterations - 1) begin
                        // Finished iterations - decide next state
                        if (cordic_mode == MODE_TAN || cordic_mode == MODE_VECTORING) begin
                            // TAN/ATAN modes: save results and proceed to correction
                            if (cordic_mode == MODE_TAN) begin
                                // For TAN: residual is z (unconsumed angle)
                                // Partial result is y (numerator of tan)
                                residual_angle <= fixed_to_fp80(z_next);
                                cordic_partial_result <= fixed_to_fp80(y_next);
                                state <= STATE_CORR_MUL_E2;  // Start correction sequence
                            end else begin
                                // For ATAN: partial result is z (accumulated angle)
                                // Residual needs to be computed as y/x (small remaining angle)
                                cordic_partial_result <= fixed_to_fp80(z_next);
                                state <= STATE_CORR_CALC_RESIDUAL;  // Compute y/x first
                            end
                        end else begin
                            // SIN/COS mode: convert output directly
                            state <= STATE_CONVERT_OUTPUT;
                        end
                    end else begin
                        iteration_count <= iteration_count + 1;
                    end
                end

                STATE_CONVERT_OUTPUT: begin
                    if (cordic_mode == MODE_ROTATION) begin
                        // Rotation mode: x ≈ cos(θ), y ≈ sin(θ)
                        cos_out <= fixed_to_fp80(x_cordic);
                        sin_out <= fixed_to_fp80(y_cordic);
                        state <= STATE_QUAD_CORRECT;
                    end else begin
                        // Vectoring mode: z ≈ atan(y/x), x*K ≈ magnitude
                        atan_out <= fixed_to_fp80(z_cordic);
                        magnitude_out <= fixed_to_fp80(x_cordic);
                        state <= STATE_DONE;
                    end
                end

                STATE_QUAD_CORRECT: begin
                    // Apply quadrant corrections
                    if (result_negate_sin) begin
                        sin_out[79] <= ~sin_out[79];  // Flip sign bit
                    end
                    if (result_negate_cos) begin
                        cos_out[79] <= ~cos_out[79];  // Flip sign bit
                    end
                    if (result_swap) begin
                        // Swap sin and cos
                        sin_out <= cos_out;
                        cos_out <= sin_out;
                    end
                    state <= STATE_DONE;
                end

                //=================================================================
                // Correction States for TAN/ATAN (Plan 2)
                //
                // For ATAN: First compute residual ε = y_final / x_final
                // For TAN: Residual ε already set to z_final
                // Then: correction = ε × (1 ± ε²/3)
                // Sequence: [y/x] → ε² → ε²×C3 → 1±ε²×C3 → ε×(1±ε²/3) → CORDIC+correction
                //=================================================================

                STATE_CORR_CALC_RESIDUAL: begin
                    // ATAN mode only: Compute residual ε = y_final / x_final
                    // For small y after 16 iterations, ε ≈ atan(y/x) ≈ y/x
                    ext_muldiv_req <= 1'b1;
                    ext_muldiv_op <= 1'b1;  // Divide
                    ext_muldiv_a <= fixed_to_fp80(y_cordic);
                    ext_muldiv_b <= fixed_to_fp80(x_cordic);
                    state <= STATE_CORR_WAIT_RESIDUAL;
                end

                STATE_CORR_WAIT_RESIDUAL: begin
                    ext_muldiv_req <= 1'b0;  // Clear request
                    if (ext_muldiv_done) begin
                        if (ext_muldiv_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            residual_angle <= ext_muldiv_result;  // ε = y/x
                            state <= STATE_CORR_MUL_E2;
                        end
                    end
                end

                STATE_CORR_MUL_E2: begin
                    // Step 1: Compute ε² = ε × ε
                    ext_muldiv_req <= 1'b1;
                    ext_muldiv_op <= 1'b0;  // Multiply
                    ext_muldiv_a <= residual_angle;
                    ext_muldiv_b <= residual_angle;
                    state <= STATE_CORR_WAIT_MUL_E2;
                end

                STATE_CORR_WAIT_MUL_E2: begin
                    ext_muldiv_req <= 1'b0;  // Clear request
                    if (ext_muldiv_done) begin
                        if (ext_muldiv_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            epsilon_squared <= ext_muldiv_result;
                            state <= STATE_CORR_MUL_C3;
                        end
                    end
                end

                STATE_CORR_MUL_C3: begin
                    // Step 2: Compute ε² × C3 (C3 = ±1/3 depending on TAN/ATAN)
                    ext_muldiv_req <= 1'b1;
                    ext_muldiv_op <= 1'b0;  // Multiply
                    ext_muldiv_a <= epsilon_squared;
                    if (cordic_mode == MODE_VECTORING) begin
                        ext_muldiv_b <= correction_c3_atan;  // -1/3 for ATAN
                    end else begin
                        ext_muldiv_b <= correction_c3_tan;   // +1/3 for TAN
                    end
                    state <= STATE_CORR_WAIT_MUL_C3;
                end

                STATE_CORR_WAIT_MUL_C3: begin
                    ext_muldiv_req <= 1'b0;
                    if (ext_muldiv_done) begin
                        if (ext_muldiv_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            epsilon_sq_times_c3 <= ext_muldiv_result;
                            state <= STATE_CORR_ADD_C1;
                        end
                    end
                end

                STATE_CORR_ADD_C1: begin
                    // Step 3: Compute 1 + ε²×C3 (which is 1 ± ε²/3)
                    ext_addsub_req <= 1'b1;
                    ext_addsub_sub <= 1'b0;  // Add
                    if (cordic_mode == MODE_VECTORING) begin
                        ext_addsub_a <= correction_c1_atan;  // 1.0
                    end else begin
                        ext_addsub_a <= correction_c1_tan;   // 1.0
                    end
                    ext_addsub_b <= epsilon_sq_times_c3;
                    state <= STATE_CORR_WAIT_ADD;
                end

                STATE_CORR_WAIT_ADD: begin
                    ext_addsub_req <= 1'b0;
                    if (ext_addsub_done) begin
                        if (ext_addsub_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            one_plus_epsilon_term <= ext_addsub_result;
                            state <= STATE_CORR_MUL_E;
                        end
                    end
                end

                STATE_CORR_MUL_E: begin
                    // Step 4: Compute ε × (1 ± ε²/3) = correction term
                    ext_muldiv_req <= 1'b1;
                    ext_muldiv_op <= 1'b0;  // Multiply
                    ext_muldiv_a <= residual_angle;
                    ext_muldiv_b <= one_plus_epsilon_term;
                    state <= STATE_CORR_WAIT_MUL_E;
                end

                STATE_CORR_WAIT_MUL_E: begin
                    ext_muldiv_req <= 1'b0;
                    if (ext_muldiv_done) begin
                        if (ext_muldiv_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            correction_value <= ext_muldiv_result;
                            state <= STATE_CORR_COMBINE;
                        end
                    end
                end

                STATE_CORR_COMBINE: begin
                    // Step 5: Add correction to CORDIC result
                    ext_addsub_req <= 1'b1;
                    ext_addsub_sub <= 1'b0;  // Add
                    ext_addsub_a <= cordic_partial_result;
                    ext_addsub_b <= correction_value;
                    state <= STATE_CORR_WAIT_COMBINE;
                end

                STATE_CORR_WAIT_COMBINE: begin
                    ext_addsub_req <= 1'b0;
                    if (ext_addsub_done) begin
                        if (ext_addsub_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            // Store final corrected result
                            if (cordic_mode == MODE_VECTORING) begin
                                atan_out <= ext_addsub_result;
                            end else begin
                                tan_out <= ext_addsub_result;
                            end
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
// This is a FUNCTIONAL CORDIC wrapper suitable for initial testing.
// Several simplifications have been made:
//
// 1. FP80 Conversion Functions:
//    - fp80_to_fixed: Simplified conversion, may have precision loss
//    - fixed_to_fp80: Incomplete normalization and rounding
//    - ENHANCEMENT: Use proper IEEE 754 pack/unpack modules
//
// 2. CORDIC Iterations:
//    - Fixed 50 iterations (good for most cases)
//    - ENHANCEMENT: Add early termination when z ≈ 0 (rotation)
//      or when y ≈ 0 (vectoring)
//
// 3. Quadrant Correction:
//    - Simple sign flipping for negate operations
//    - ENHANCEMENT: Use proper FP negate with rounding
//
// 4. Error Handling:
//    - Basic error propagation from range reduction
//    - ENHANCEMENT: Add overflow/underflow detection in conversions
//
// 5. Performance:
//    - Current: ~55 cycles (50 iterations + overhead)
//    - ENHANCEMENT: Pipeline CORDIC iterations for higher throughput
//
// TESTING STRATEGY:
// 1. Test with known angles: 0, π/6, π/4, π/3, π/2
// 2. Verify sin²(θ) + cos²(θ) = 1 identity
// 3. Compare against Python math.sin(), math.cos()
// 4. Measure ULP error across input range
//
// FUTURE ENHANCEMENTS:
// - Integrate with proper FP pack/unpack modules
// - Add exception flag outputs (invalid, overflow, underflow)
// - Optimize conversion functions for speed and accuracy
// - Add configurable iteration count for speed/accuracy trade-off
//=====================================================================
