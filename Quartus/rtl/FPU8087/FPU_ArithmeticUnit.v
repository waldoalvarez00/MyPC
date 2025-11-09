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
    input wire [3:0]  operation,        // Operation selector
    input wire        enable,           // Start operation
    input wire [1:0]  rounding_mode,    // Rounding mode

    // Operands (80-bit FP)
    input wire [79:0] operand_a,
    input wire [79:0] operand_b,

    // Integer operands (for conversions)
    input wire signed [15:0] int16_in,
    input wire signed [31:0] int32_in,

    // FP32/64 operands (for conversions)
    input wire [31:0] fp32_in,
    input wire [63:0] fp64_in,

    // Result
    output reg [79:0] result,
    output reg signed [15:0] int16_out,
    output reg signed [31:0] int32_out,
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

    // Transcendental operations (12-20)
    localparam OP_SQRT     = 4'd12;
    localparam OP_SIN      = 4'd13;
    localparam OP_COS      = 4'd14;
    localparam OP_SINCOS   = 4'd15;  // Note: Returns two values

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

    // Multiply
    wire [79:0] mul_result;
    wire mul_done, mul_invalid, mul_overflow, mul_underflow, mul_inexact;

    FPU_IEEE754_Multiply mul_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_MUL),
        .operand_a(operand_a),
        .operand_b(operand_b),
        .rounding_mode(rounding_mode),
        .result(mul_result),
        .done(mul_done),
        .flag_invalid(mul_invalid),
        .flag_overflow(mul_overflow),
        .flag_underflow(mul_underflow),
        .flag_inexact(mul_inexact)
    );

    // Divide
    wire [79:0] div_result;
    wire div_done, div_invalid, div_div_by_zero, div_overflow, div_underflow, div_inexact;

    FPU_IEEE754_Divide div_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_DIV),
        .operand_a(operand_a),
        .operand_b(operand_b),
        .rounding_mode(rounding_mode),
        .result(div_result),
        .done(div_done),
        .flag_invalid(div_invalid),
        .flag_div_by_zero(div_div_by_zero),
        .flag_overflow(div_overflow),
        .flag_underflow(div_underflow),
        .flag_inexact(div_inexact)
    );

    //=================================================================
    // Conversion Units
    //=================================================================

    // Int16 to FP80
    wire [79:0] int16_to_fp_result;
    wire int16_to_fp_done;

    FPU_Int16_to_FP80 int16_to_fp_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_INT16_TO_FP),
        .int_in(int16_in),
        .fp_out(int16_to_fp_result),
        .done(int16_to_fp_done)
    );

    // Int32 to FP80
    wire [79:0] int32_to_fp_result;
    wire int32_to_fp_done;

    FPU_Int32_to_FP80 int32_to_fp_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_INT32_TO_FP),
        .int_in(int32_in),
        .fp_out(int32_to_fp_result),
        .done(int32_to_fp_done)
    );

    // FP80 to Int16
    wire signed [15:0] fp_to_int16_result;
    wire fp_to_int16_done, fp_to_int16_invalid, fp_to_int16_overflow, fp_to_int16_inexact;

    FPU_FP80_to_Int16 fp_to_int16_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_FP_TO_INT16),
        .fp_in(operand_a),
        .rounding_mode(rounding_mode),
        .int_out(fp_to_int16_result),
        .done(fp_to_int16_done),
        .flag_invalid(fp_to_int16_invalid),
        .flag_overflow(fp_to_int16_overflow),
        .flag_inexact(fp_to_int16_inexact)
    );

    // FP80 to Int32
    wire signed [31:0] fp_to_int32_result;
    wire fp_to_int32_done, fp_to_int32_invalid, fp_to_int32_overflow, fp_to_int32_inexact;

    FPU_FP80_to_Int32 fp_to_int32_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_FP_TO_INT32),
        .fp_in(operand_a),
        .rounding_mode(rounding_mode),
        .int_out(fp_to_int32_result),
        .done(fp_to_int32_done),
        .flag_invalid(fp_to_int32_invalid),
        .flag_overflow(fp_to_int32_overflow),
        .flag_inexact(fp_to_int32_inexact)
    );

    // FP32 to FP80
    wire [79:0] fp32_to_fp80_result;
    wire fp32_to_fp80_done;

    FPU_FP32_to_FP80 fp32_to_fp80_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_FP32_TO_FP80),
        .fp32_in(fp32_in),
        .fp80_out(fp32_to_fp80_result),
        .done(fp32_to_fp80_done)
    );

    // FP64 to FP80
    wire [79:0] fp64_to_fp80_result;
    wire fp64_to_fp80_done;

    FPU_FP64_to_FP80 fp64_to_fp80_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_FP64_TO_FP80),
        .fp64_in(fp64_in),
        .fp80_out(fp64_to_fp80_result),
        .done(fp64_to_fp80_done)
    );

    // FP80 to FP32
    wire [31:0] fp80_to_fp32_result;
    wire fp80_to_fp32_done, fp80_to_fp32_invalid, fp80_to_fp32_overflow;
    wire fp80_to_fp32_underflow, fp80_to_fp32_inexact;

    FPU_FP80_to_FP32 fp80_to_fp32_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_FP80_TO_FP32),
        .fp80_in(operand_a),
        .rounding_mode(rounding_mode),
        .fp32_out(fp80_to_fp32_result),
        .done(fp80_to_fp32_done),
        .flag_invalid(fp80_to_fp32_invalid),
        .flag_overflow(fp80_to_fp32_overflow),
        .flag_underflow(fp80_to_fp32_underflow),
        .flag_inexact(fp80_to_fp32_inexact)
    );

    // FP80 to FP64
    wire [63:0] fp80_to_fp64_result;
    wire fp80_to_fp64_done, fp80_to_fp64_invalid, fp80_to_fp64_overflow;
    wire fp80_to_fp64_underflow, fp80_to_fp64_inexact;

    FPU_FP80_to_FP64 fp80_to_fp64_unit (
        .clk(clk),
        .reset(reset),
        .enable(enable && operation == OP_FP80_TO_FP64),
        .fp80_in(operand_a),
        .rounding_mode(rounding_mode),
        .fp64_out(fp80_to_fp64_result),
        .done(fp80_to_fp64_done),
        .flag_invalid(fp80_to_fp64_invalid),
        .flag_overflow(fp80_to_fp64_overflow),
        .flag_underflow(fp80_to_fp64_underflow),
        .flag_inexact(fp80_to_fp64_inexact)
    );

    //=================================================================
    // Transcendental Functions Unit
    //=================================================================

    // Map operation codes to transcendental operation codes
    wire [3:0] trans_operation = operation - 4'd12;  // Map 12-20 to 0-8
    wire trans_enable = enable && (operation >= 4'd12 && operation <= 4'd15);

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
    // Output Multiplexing
    //=================================================================

    always @(*) begin
        // Default values
        result = 80'd0;
        int16_out = 16'd0;
        int32_out = 32'd0;
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

        // Select outputs based on operation
        case (operation)
            OP_ADD, OP_SUB: begin
                result = addsub_result;
                done = addsub_done;
                cc_equal = addsub_cmp_equal;
                cc_less = addsub_cmp_less;
                cc_greater = addsub_cmp_greater;
                flag_invalid = addsub_invalid;
                flag_overflow = addsub_overflow;
                flag_underflow = addsub_underflow;
                flag_inexact = addsub_inexact;
            end

            OP_MUL: begin
                result = mul_result;
                done = mul_done;
                flag_invalid = mul_invalid;
                flag_overflow = mul_overflow;
                flag_underflow = mul_underflow;
                flag_inexact = mul_inexact;
            end

            OP_DIV: begin
                result = div_result;
                done = div_done;
                flag_invalid = div_invalid;
                flag_zero_divide = div_div_by_zero;
                flag_overflow = div_overflow;
                flag_underflow = div_underflow;
                flag_inexact = div_inexact;
            end

            OP_INT16_TO_FP: begin
                result = int16_to_fp_result;
                done = int16_to_fp_done;
            end

            OP_INT32_TO_FP: begin
                result = int32_to_fp_result;
                done = int32_to_fp_done;
            end

            OP_FP_TO_INT16: begin
                int16_out = fp_to_int16_result;
                done = fp_to_int16_done;
                flag_invalid = fp_to_int16_invalid;
                flag_overflow = fp_to_int16_overflow;
                flag_inexact = fp_to_int16_inexact;
            end

            OP_FP_TO_INT32: begin
                int32_out = fp_to_int32_result;
                done = fp_to_int32_done;
                flag_invalid = fp_to_int32_invalid;
                flag_overflow = fp_to_int32_overflow;
                flag_inexact = fp_to_int32_inexact;
            end

            OP_FP32_TO_FP80: begin
                result = fp32_to_fp80_result;
                done = fp32_to_fp80_done;
            end

            OP_FP64_TO_FP80: begin
                result = fp64_to_fp80_result;
                done = fp64_to_fp80_done;
            end

            OP_FP80_TO_FP32: begin
                fp32_out = fp80_to_fp32_result;
                done = fp80_to_fp32_done;
                flag_invalid = fp80_to_fp32_invalid;
                flag_overflow = fp80_to_fp32_overflow;
                flag_underflow = fp80_to_fp32_underflow;
                flag_inexact = fp80_to_fp32_inexact;
            end

            OP_FP80_TO_FP64: begin
                fp64_out = fp80_to_fp64_result;
                done = fp80_to_fp64_done;
                flag_invalid = fp80_to_fp64_invalid;
                flag_overflow = fp80_to_fp64_overflow;
                flag_underflow = fp80_to_fp64_underflow;
                flag_inexact = fp80_to_fp64_inexact;
            end

            // Transcendental operations
            OP_SQRT, OP_SIN, OP_COS, OP_SINCOS: begin
                result = trans_result_primary;
                done = trans_done;
                flag_invalid = trans_error;
                // Note: OP_SINCOS has secondary result (cos) in trans_result_secondary
                // This will be handled by FPU_Core for stack operations
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
// Added Operations (4-bit operation code):
// - OP_SQRT  (12): Square root
// - OP_SIN   (13): Sine
// - OP_COS   (14): Cosine
// - OP_SINCOS(15): Both sine and cosine
//
// Additional transcendental operations (16-20) can be added when needed:
// - OP_TAN    (16): Tangent
// - OP_ATAN   (17): Arctangent
// - OP_F2XM1  (18): 2^x - 1
// - OP_FYL2X  (19): y × log₂(x)
// - OP_FYL2XP1(20): y × log₂(x+1)
//
// Note: These require 5-bit operation codes or extended encoding.
//
// FSINCOS Special Handling:
// The FSINCOS operation returns TWO results:
// - result_primary: sin(angle)
// - result_secondary: cos(angle)
//
// The FPU_Core instruction decoder must handle this by:
// 1. Pushing sin result to stack
// 2. Pushing cos result to stack
// This requires special case logic in FPU_Core state machine.
//
// Integration Complete: ✅
// - Transcendental unit instantiated
// - Operation codes defined (12-15)
// - Output multiplexing extended
// - Ready for FPU_Core instruction integration
//=====================================================================
