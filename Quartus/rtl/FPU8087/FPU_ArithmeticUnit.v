`timescale 1ns / 1ps

//=====================================================================
// FPU Arithmetic Unit Wrapper
//
// Combines all arithmetic and conversion operations:
// - Add/Subtract
// - Multiply
// - Divide
// - Integer conversion (Int16/32 ↔ FP80)
// - Format conversion (FP32/64 ↔ FP80)
//
// Provides unified interface with operation selection
//=====================================================================

module FPU_ArithmeticUnit(
    input wire clk,
    input wire reset,

    // Operation control
    input wire [4:0]  operation,        // Operation selector (5 bits: 0-17 for BCD)
    input wire        enable,           // Start operation
    input wire [1:0]  rounding_mode,    // Rounding mode
    input wire [1:0]  precision_mode,   // Precision control (00=24-bit, 10=53-bit, 11=64-bit)

    // Operands (80-bit FP)
    input wire [79:0] operand_a,
    input wire [79:0] operand_b,

    // Integer operands (for conversions)
    input wire signed [15:0] int16_in,
    input wire signed [31:0] int32_in,
    input wire [63:0] uint64_in,       // Unsigned 64-bit for BCD conversion
    input wire        uint64_sign_in,  // Sign bit for uint64

    // FP32/64 operands (for conversions)
    input wire [31:0] fp32_in,
    input wire [63:0] fp64_in,

    // Result
    output reg [79:0] result,
    output reg [79:0] result_secondary,    // Secondary result (for FSINCOS, FPTAN)
    output reg        has_secondary,        // Flag: secondary result is valid
    output reg signed [15:0] int16_out,
    output reg signed [31:0] int32_out,
    output reg [63:0] uint64_out,          // Unsigned 64-bit for BCD conversion
    output reg        uint64_sign_out,     // Sign bit for uint64
    output reg [31:0] fp32_out,
    output reg [63:0] fp64_out,
    output reg        done,

    // Condition codes (for comparisons)
    output reg        cc_less,
    output reg        cc_equal,
    output reg        cc_greater,
    output reg        cc_unordered,

    // Exception flags
    output reg        flag_invalid,
    output reg        flag_denormal,
    output reg        flag_zero_divide,
    output reg        flag_overflow,
    output reg        flag_underflow,
    output reg        flag_inexact
);

    //=================================================================
    // Operation Codes
    //=================================================================

    localparam OP_ADD        = 4'd0;
    localparam OP_SUB        = 4'd1;
    localparam OP_MUL        = 4'd2;
    localparam OP_DIV        = 4'd3;
    localparam OP_INT16_TO_FP = 4'd4;
    localparam OP_INT32_TO_FP = 4'd5;
    localparam OP_FP_TO_INT16 = 4'd6;
    localparam OP_FP_TO_INT32 = 4'd7;
    localparam OP_FP32_TO_FP80 = 4'd8;
    localparam OP_FP64_TO_FP80 = 4'd9;
    localparam OP_FP80_TO_FP32 = 4'd10;
    localparam OP_FP80_TO_FP64 = 4'd11;

    // Transcendental operations (12-15)
    localparam OP_SQRT     = 4'd12;
    localparam OP_SIN      = 4'd13;
    localparam OP_COS      = 4'd14;
    localparam OP_SINCOS   = 4'd15;  // Note: Returns two values

    // BCD conversion operations (for FBLD/FBSTP)
    // Note: These operate on unsigned 64-bit integers with separate sign
    localparam OP_UINT64_TO_FP = 5'd16;  // UInt64 + sign → FP80
    localparam OP_FP_TO_UINT64 = 5'd17;  // FP80 → UInt64 + sign

    // Advanced transcendental operations
    localparam OP_TAN      = 5'd18;  // Tangent (FPTAN)
    localparam OP_ATAN     = 5'd19;  // Arctangent (FPATAN)
    localparam OP_F2XM1    = 5'd20;  // 2^x - 1
    localparam OP_FYL2X    = 5'd21;  // y × log₂(x)
    localparam OP_FYL2XP1  = 5'd22;  // y × log₂(x+1)

    // Bit manipulation operations
    localparam OP_FXTRACT  = 5'd23;  // Extract exponent and significand
    localparam OP_FSCALE   = 5'd24;  // Scale by power of 2

    //=================================================================
    // Arithmetic Units
    //=================================================================

    // Add/Subtract
    wire [79:0] addsub_result;
    wire addsub_done, addsub_cmp_equal, addsub_cmp_less, addsub_cmp_greater;
    wire addsub_invalid, addsub_overflow, addsub_underflow, addsub_inexact;

    FPU_IEEE754_AddSub addsub_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && (operation == OP_ADD || operation == OP_SUB)),
        .operand_a(operand_a),
        .operand_b(operand_b),
        .subtract(operation == OP_SUB),
        .rounding_mode(rounding_mode),
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
    // Unified Multiply/Divide Unit (AREA OPTIMIZED - Phase 2)
    // Replaces separate multiply and divide modules (~757 lines → ~550 lines)
    // Area reduction: ~25% for MulDiv logic (8-10% total FPU)
    //=================================================================

    wire muldiv_enable = enable && (operation == OP_MUL || operation == OP_DIV);
    wire muldiv_operation = (operation == OP_DIV);  // 0=mul, 1=div

    wire [79:0] muldiv_result;
    wire muldiv_done, muldiv_invalid, muldiv_div_by_zero;
    wire muldiv_overflow, muldiv_underflow, muldiv_inexact;

    FPU_IEEE754_MulDiv_Unified muldiv_unit (
        .clk(clk),
        .reset(reset),
        .enable(muldiv_enable),
        .operation(muldiv_operation),
        .operand_a(operand_a),
        .operand_b(operand_b),
        .rounding_mode(rounding_mode),
        .result(muldiv_result),
        .done(muldiv_done),
        .flag_invalid(muldiv_invalid),
        .flag_div_by_zero(muldiv_div_by_zero),
        .flag_overflow(muldiv_overflow),
        .flag_underflow(muldiv_underflow),
        .flag_inexact(muldiv_inexact)
    );

    //=================================================================
    // Unified Format Converter (AREA OPTIMIZED)
    // Replaces 10 separate converter modules (~1600 lines → ~600 lines)
    // Area reduction: ~60% for format conversion logic
    //=================================================================

    // Map operation codes to converter modes
    wire [3:0] conv_mode;
    assign conv_mode = (operation == OP_FP32_TO_FP80)  ? 4'd0 :
                       (operation == OP_FP64_TO_FP80)  ? 4'd1 :
                       (operation == OP_FP80_TO_FP32)  ? 4'd2 :
                       (operation == OP_FP80_TO_FP64)  ? 4'd3 :
                       (operation == OP_INT16_TO_FP)   ? 4'd4 :
                       (operation == OP_INT32_TO_FP)   ? 4'd5 :
                       (operation == OP_FP_TO_INT16)   ? 4'd6 :
                       (operation == OP_FP_TO_INT32)   ? 4'd7 :
                       (operation == OP_UINT64_TO_FP)  ? 4'd8 :
                       (operation == OP_FP_TO_UINT64)  ? 4'd9 : 4'd15;

    // Enable signal for converter
    wire conv_enable = enable && ((operation >= OP_INT16_TO_FP && operation <= OP_FP80_TO_FP64) ||
                                   operation == OP_UINT64_TO_FP || operation == OP_FP_TO_UINT64);

    // Unified converter outputs
    wire [79:0] conv_fp80_out;
    wire [63:0] conv_fp64_out;
    wire [31:0] conv_fp32_out;
    wire [63:0] conv_uint64_out;
    wire signed [31:0] conv_int32_out;
    wire signed [15:0] conv_int16_out;
    wire        conv_uint64_sign_out;
    wire        conv_done;
    wire        conv_invalid, conv_overflow, conv_underflow, conv_inexact;

    FPU_Format_Converter_Unified unified_converter (
        .clk(clk),
        .reset(reset),
        .enable(conv_enable),
        .mode(conv_mode),

        // Inputs
        .fp80_in(operand_a),
        .fp64_in(fp64_in),
        .fp32_in(fp32_in),
        .uint64_in(uint64_in),
        .int32_in(int32_in),
        .int16_in(int16_in),
        .uint64_sign(uint64_sign_in),
        .rounding_mode(rounding_mode),

        // Outputs
        .fp80_out(conv_fp80_out),
        .fp64_out(conv_fp64_out),
        .fp32_out(conv_fp32_out),
        .uint64_out(conv_uint64_out),
        .int32_out(conv_int32_out),
        .int16_out(conv_int16_out),
        .uint64_sign_out(conv_uint64_sign_out),
        .done(conv_done),

        // Exception flags
        .flag_invalid(conv_invalid),
        .flag_overflow(conv_overflow),
        .flag_underflow(conv_underflow),
        .flag_inexact(conv_inexact)
    );

    //=================================================================
    // Transcendental Functions Unit
    //=================================================================

    // Map operation codes to transcendental operation codes
    // Basic transcendentals: 12-15 → 0-3
    // Advanced transcendentals: 18-22 → 4-8
    wire [3:0] trans_operation = (operation >= 5'd18) ? (operation - 5'd14) : (operation - 4'd12);
    wire trans_enable = enable && ((operation >= 4'd12 && operation <= 4'd15) ||
                                     (operation >= 5'd18 && operation <= 5'd22));

    wire [79:0] trans_result_primary, trans_result_secondary;
    wire trans_has_secondary;
    wire trans_done, trans_error;

    FPU_Transcendental trans_unit (
        .clk(clk),
        .reset(reset),
        .operation(trans_operation),
        .enable(trans_enable),
        .operand_a(operand_a),
        .operand_b(operand_b),
        .result_primary(trans_result_primary),
        .result_secondary(trans_result_secondary),
        .has_secondary(trans_has_secondary),
        .done(trans_done),
        .error(trans_error)
    );

    //=================================================================
    // Bit Manipulation Operations (FXTRACT, FSCALE)
    //=================================================================

    // Helper functions for detection
    function automatic is_zero_helper;
        input [79:0] fp_value;
        begin
            is_zero_helper = (fp_value[78:0] == 79'd0);
        end
    endfunction

    function automatic is_infinity_helper;
        input [79:0] fp_value;
        begin
            is_infinity_helper = (fp_value[78:64] == 15'h7FFF) &&
                                (fp_value[63:0] == 64'h8000_0000_0000_0000);
        end
    endfunction

    function automatic is_nan_helper;
        input [79:0] fp_value;
        begin
            is_nan_helper = (fp_value[78:64] == 15'h7FFF) &&
                           (fp_value[63:0] != 64'h8000_0000_0000_0000);
        end
    endfunction

    function automatic [79:0] make_infinity_helper;
        input sign;
        begin
            make_infinity_helper = {sign, 15'h7FFF, 64'h8000_0000_0000_0000};
        end
    endfunction

    function automatic [79:0] make_zero_helper;
        input sign;
        begin
            make_zero_helper = {sign, 79'd0};
        end
    endfunction

    // Check if FP80 value is denormal (exponent = 0, mantissa ≠ 0)
    function automatic is_denormal_helper;
        input [79:0] fp_value;
        begin
            is_denormal_helper = (fp_value[78:64] == 15'd0) && (fp_value[63:0] != 64'd0);
        end
    endfunction

    // Helper: Convert signed 16-bit integer to FP80
    function automatic [79:0] int16_to_fp80;
        input signed [15:0] int_val;
        reg sign_bit;
        reg [15:0] abs_val;
        reg [14:0] biased_exp;
        reg [63:0] mantissa;
        integer i;
        integer msb_pos;
        begin
            if (int_val == 0) begin
                int16_to_fp80 = 80'h0000_0000_0000_0000_0000;
            end else begin
                // Get sign and absolute value
                sign_bit = int_val[15];
                abs_val = sign_bit ? -int_val : int_val;

                // Find MSB position (leading one)
                msb_pos = 0;
                for (i = 15; i >= 0; i = i - 1) begin
                    if (abs_val[i]) begin
                        msb_pos = i;
                        i = -1;  // Break loop
                    end
                end

                // Biased exponent = 16383 + msb_pos
                biased_exp = 15'd16383 + msb_pos;

                // Mantissa: shift abs_val left to put MSB at bit 63 (integer bit)
                // First zero-extend abs_val to 64 bits, then shift
                mantissa = {48'd0, abs_val} << (63 - msb_pos);

                int16_to_fp80 = {sign_bit, biased_exp, mantissa};
            end
        end
    endfunction

    // FXTRACT: Extract exponent and significand
    // Full implementation
    reg [79:0] fxtract_significand;
    reg [79:0] fxtract_exponent;
    reg        fxtract_done;

    always @(*) begin
        fxtract_done = enable && (operation == OP_FXTRACT);

        // Extract significand (mantissa normalized to [1.0, 2.0))
        if (is_zero_helper(operand_a) || is_infinity_helper(operand_a) || is_nan_helper(operand_a)) begin
            // Special values remain unchanged
            fxtract_significand = operand_a;
        end else begin
            // Normal case: set exponent to 3FFF (bias for exponent 0)
            // This gives a value in range [1.0, 2.0)
            fxtract_significand = {operand_a[79], 15'h3FFF, operand_a[63:0]};
        end

        // Extract exponent as FP80 value
        if (is_zero_helper(operand_a)) begin
            // Zero → exponent is -Infinity
            fxtract_exponent = make_infinity_helper(1'b1);
        end else if (is_infinity_helper(operand_a)) begin
            // Infinity → exponent is +Infinity
            fxtract_exponent = make_infinity_helper(1'b0);
        end else if (is_nan_helper(operand_a)) begin
            // NaN → propagate NaN
            fxtract_exponent = operand_a;
        end else begin
            // Normal case: convert (biased_exp - 16383) to FP80
            // True exponent = biased_exp - 16383
            // First extend to 16 bits, then subtract
            fxtract_exponent = int16_to_fp80($signed({1'b0, operand_a[78:64]}) - 16'sd16383);
        end
    end

    // FSCALE: Scale by power of 2
    // Full implementation: ST(0) × 2^(round_to_int(ST(1)))
    reg [79:0] fscale_result;
    reg        fscale_done;
    reg signed [31:0] scale_int;
    reg signed [31:0] new_exp;

    always @(*) begin
        fscale_done = enable && (operation == OP_FSCALE);

        // Extract integer scale value from operand_b (ST(1))
        if (operand_b[78:64] < 15'd16383) begin
            // Scale < 1, round to 0
            scale_int = 0;
        end else if (operand_b[78:64] <= 15'd16398) begin
            // Exponent 0-15: extract integer part
            // For FP80, value = mantissa × 2^(exponent - 16383)
            // Integer part = mantissa >> (63 - (exponent - 16383))
            scale_int = operand_b[63:0] >> (7'd63 - (operand_b[78:64] - 15'd16383));
            if (operand_b[79]) scale_int = -scale_int;
        end else begin
            // Very large - saturate
            scale_int = operand_b[79] ? -32'sd16384 : 32'sd16384;
        end

        // Special cases for operand_a (value to scale)
        if (is_nan_helper(operand_a) || is_nan_helper(operand_b)) begin
            // NaN propagation - return first NaN
            fscale_result = is_nan_helper(operand_a) ? operand_a : operand_b;
        end else if (is_zero_helper(operand_a)) begin
            // 0 × 2^n = 0
            fscale_result = operand_a;
        end else if (is_infinity_helper(operand_a)) begin
            // Inf × 2^n = Inf
            fscale_result = operand_a;
        end else if (is_infinity_helper(operand_b)) begin
            // value × 2^(±Inf)
            if (operand_b[79]) begin
                // 2^(-Inf) = 0
                fscale_result = make_zero_helper(operand_a[79]);
            end else begin
                // 2^(+Inf) = Inf
                fscale_result = make_infinity_helper(operand_a[79]);
            end
        end else begin
            // Normal case: add scale to exponent
            new_exp = $signed({17'd0, operand_a[78:64]}) + scale_int;

            // Check for overflow/underflow
            if (new_exp > 32'sd32766) begin
                // Overflow → Infinity
                fscale_result = make_infinity_helper(operand_a[79]);
            end else if (new_exp < -32'sd16382) begin
                // Underflow → Zero
                fscale_result = make_zero_helper(operand_a[79]);
            end else begin
                // Normal result
                fscale_result = {operand_a[79], new_exp[14:0], operand_a[63:0]};
            end
        end
    end

    //=================================================================
    // Output Multiplexing
    //=================================================================

    always @(*) begin
        // Default values
        result = 80'd0;
        result_secondary = 80'd0;
        has_secondary = 1'b0;
        int16_out = 16'd0;
        int32_out = 32'd0;
        uint64_out = 64'd0;
        uint64_sign_out = 1'b0;
        fp32_out = 32'd0;
        fp64_out = 64'd0;
        done = 1'b0;

        cc_less = 1'b0;
        cc_equal = 1'b0;
        cc_greater = 1'b0;
        cc_unordered = 1'b0;

        flag_invalid = 1'b0;
        flag_denormal = 1'b0;
        flag_zero_divide = 1'b0;
        flag_overflow = 1'b0;
        flag_underflow = 1'b0;
        flag_inexact = 1'b0;

        // Check for denormal operands (except for conversion operations)
        if (enable && (operation <= OP_DIV || operation == OP_SQRT ||
                      operation == OP_SIN || operation == OP_COS || operation == OP_SINCOS ||
                      operation == OP_TAN || operation == OP_ATAN || operation == OP_F2XM1 ||
                      operation == OP_FYL2X || operation == OP_FYL2XP1 ||
                      operation == OP_FXTRACT || operation == OP_FSCALE)) begin
            if (is_denormal_helper(operand_a) || is_denormal_helper(operand_b)) begin
                flag_denormal = 1'b1;
            end
        end

        // Select outputs based on operation
        case (operation)
            OP_ADD, OP_SUB: begin
                result = addsub_result;
                done = addsub_done;
                cc_equal = addsub_cmp_equal;
                cc_less = addsub_cmp_less;
                cc_greater = addsub_cmp_greater;
                // Unordered if all comparison flags are false (NaN comparison)
                cc_unordered = ~addsub_cmp_equal & ~addsub_cmp_less & ~addsub_cmp_greater;
                flag_invalid = addsub_invalid;
                flag_overflow = addsub_overflow;
                flag_underflow = addsub_underflow;
                flag_inexact = addsub_inexact;
            end

            // Both multiply and divide now use unified MulDiv module
            OP_MUL, OP_DIV: begin
                result = muldiv_result;
                done = muldiv_done;
                flag_invalid = muldiv_invalid;
                flag_zero_divide = muldiv_div_by_zero;
                flag_overflow = muldiv_overflow;
                flag_underflow = muldiv_underflow;
                flag_inexact = muldiv_inexact;
            end

            // All format conversion operations now use unified converter
            OP_INT16_TO_FP, OP_INT32_TO_FP, OP_FP32_TO_FP80, OP_FP64_TO_FP80,
            OP_UINT64_TO_FP: begin
                result = conv_fp80_out;
                done = conv_done;
                flag_invalid = conv_invalid;
                flag_overflow = conv_overflow;
                flag_inexact = conv_inexact;
            end

            OP_FP_TO_INT16: begin
                int16_out = conv_int16_out;
                done = conv_done;
                flag_invalid = conv_invalid;
                flag_overflow = conv_overflow;
                flag_inexact = conv_inexact;
            end

            OP_FP_TO_INT32: begin
                int32_out = conv_int32_out;
                done = conv_done;
                flag_invalid = conv_invalid;
                flag_overflow = conv_overflow;
                flag_inexact = conv_inexact;
            end

            OP_FP80_TO_FP32: begin
                fp32_out = conv_fp32_out;
                done = conv_done;
                flag_invalid = conv_invalid;
                flag_overflow = conv_overflow;
                flag_underflow = conv_underflow;
                flag_inexact = conv_inexact;
            end

            OP_FP80_TO_FP64: begin
                fp64_out = conv_fp64_out;
                done = conv_done;
                flag_invalid = conv_invalid;
                flag_overflow = conv_overflow;
                flag_underflow = conv_underflow;
                flag_inexact = conv_inexact;
            end

            // BCD conversion operations (also use unified converter)
            OP_FP_TO_UINT64: begin
                uint64_out = conv_uint64_out;
                uint64_sign_out = conv_uint64_sign_out;
                done = conv_done;
                flag_invalid = conv_invalid;
                flag_overflow = conv_overflow;
                flag_inexact = conv_inexact;
            end

            // Transcendental operations
            OP_SQRT, OP_SIN, OP_COS, OP_SINCOS,
            OP_TAN, OP_ATAN, OP_F2XM1, OP_FYL2X, OP_FYL2XP1: begin
                result = trans_result_primary;
                result_secondary = trans_result_secondary;
                has_secondary = trans_has_secondary;
                done = trans_done;
                flag_invalid = trans_error;
                // Note: OP_SINCOS sets has_secondary=1 with cos(θ) in result_secondary
                // Note: OP_TAN may set has_secondary for special implementations
            end

            // Bit manipulation operations
            OP_FXTRACT: begin
                result = fxtract_significand;
                result_secondary = fxtract_exponent;
                has_secondary = 1'b1;  // FXTRACT returns two values
                done = fxtract_done;
            end

            OP_FSCALE: begin
                result = fscale_result;
                done = fscale_done;
            end

            default: begin
                done = 1'b0;
            end
        endcase
    end

endmodule


//=====================================================================
// TRANSCENDENTAL OPERATIONS INTEGRATION NOTES
//=====================================================================
//
// Basic Transcendental Operations (4-bit operation codes 12-15):
// - OP_SQRT  (12): Square root
// - OP_SIN   (13): Sine
// - OP_COS   (14): Cosine
// - OP_SINCOS(15): Both sine and cosine
//
// Advanced Transcendental Operations (5-bit operation codes 18-22):
// - OP_TAN    (18): Tangent (FPTAN)
// - OP_ATAN   (19): Arctangent (FPATAN)
// - OP_F2XM1  (20): 2^x - 1
// - OP_FYL2X  (21): y × log₂(x)
// - OP_FYL2XP1(22): y × log₂(x+1)
//
// Special Multi-Result Operations:
// - FSINCOS: Returns sin(angle) and cos(angle) in dual results
// - FPTAN: Returns tan(angle) and pushes 1.0 (for compatibility)
//
// The FPU_Core instruction decoder must handle multi-result operations by:
// 1. Pushing primary result to stack
// 2. Pushing secondary result to stack (if has_secondary=1)
// This requires special case logic in FPU_Core state machine.
//
// Integration Complete: ✅
// - Transcendental unit instantiated
// - Basic operation codes defined (12-15)
// - Advanced operation codes defined (18-22)
// - Output multiplexing extended
// - Ready for FPU_Core instruction integration
//=====================================================================
