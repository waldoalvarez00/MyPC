`timescale 1ns / 1ps

//=====================================================================
// IEEE 754 Extended Precision (80-bit) Divide Unit
//
// Implements proper floating-point division according to
// IEEE 754 standard for 80-bit extended precision format.
//
// Format: [79:Sign][78:64:Exponent][63:Integer][62:0:Fraction]
//
// Features:
// - 64-bit ÷ 64-bit mantissa division
// - Proper exponent subtraction with bias correction
// - Normalization after division
// - Rounding according to IEEE 754 modes
// - Special value handling (±0, ±∞, NaN)
// - Exception detection (invalid, divide-by-zero, overflow, underflow, inexact)
//=====================================================================

module FPU_IEEE754_Divide(
    input wire clk,
    input wire reset,
    input wire enable,                  // Start operation

    // Operands
    input wire [79:0] operand_a,       // Dividend (80-bit)
    input wire [79:0] operand_b,       // Divisor (80-bit)

    // Control
    input wire [1:0]  rounding_mode,   // 00=nearest, 01=down, 10=up, 11=truncate

    // Result
    output reg [79:0] result,          // Result (80-bit)
    output reg        done,            // Operation complete

    // Exception flags
    output reg        flag_invalid,    // Invalid operation (0÷0, ∞÷∞)
    output reg        flag_div_by_zero,// Division by zero
    output reg        flag_overflow,   // Result overflow
    output reg        flag_underflow,  // Result underflow
    output reg        flag_inexact     // Result not exact (rounded)
);

    //=================================================================
    // Internal States
    //=================================================================

    localparam STATE_IDLE       = 3'd0;
    localparam STATE_UNPACK     = 3'd1;
    localparam STATE_DIVIDE     = 3'd2;
    localparam STATE_NORMALIZE  = 3'd3;
    localparam STATE_ROUND      = 3'd4;
    localparam STATE_PACK       = 3'd5;

    reg [2:0] state;

    //=================================================================
    // Unpacked Operands
    //=================================================================

    // Operand A (dividend)
    reg        sign_a;
    reg [14:0] exp_a;
    reg [63:0] mant_a;
    reg        is_zero_a, is_inf_a, is_nan_a;

    // Operand B (divisor)
    reg        sign_b;
    reg [14:0] exp_b;
    reg [63:0] mant_b;
    reg        is_zero_b, is_inf_b, is_nan_b;

    //=================================================================
    // Working Registers
    //=================================================================

    reg        result_sign;
    reg signed [16:0] result_exp;   // 17-bit signed to handle overflow/underflow
    reg signed [128:0] remainder;   // Signed partial remainder (129-bit for sign)
    reg [63:0]  divisor;            // Divisor
    reg [66:0]  quotient;           // Quotient with guard/round/sticky
    reg [66:0]  result_mant;        // Normalized result with guard/round/sticky

    reg        round_bit, sticky_bit;
    reg [6:0]  div_count;           // Division iteration counter
    reg        remainder_negative;  // Track if remainder is negative
    reg        pre_shifted;         // Flag: dividend was pre-shifted for mant_a < mant_b
    reg        do_subtract;         // Temp flag for division iteration

    //=================================================================
    // Special Value Detection
    //=================================================================

    task detect_special_a;
        begin
            is_zero_a = (exp_a == 15'd0) && (mant_a == 64'd0);
            is_inf_a = (exp_a == 15'h7FFF) && (mant_a[62:0] == 63'd0) && (mant_a[63] == 1'b1);
            is_nan_a = (exp_a == 15'h7FFF) && ((mant_a[62:0] != 63'd0) || (mant_a[63] == 1'b0));
        end
    endtask

    task detect_special_b;
        begin
            is_zero_b = (exp_b == 15'd0) && (mant_b == 64'd0);
            is_inf_b = (exp_b == 15'h7FFF) && (mant_b[62:0] == 63'd0) && (mant_b[63] == 1'b1);
            is_nan_b = (exp_b == 15'h7FFF) && ((mant_b[62:0] != 63'd0) || (mant_b[63] == 1'b0));
        end
    endtask

    //=================================================================
    // Main State Machine
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_IDLE;
            done <= 1'b0;
            result <= 80'd0;
            flag_invalid <= 1'b0;
            flag_div_by_zero <= 1'b0;
            flag_overflow <= 1'b0;
            flag_underflow <= 1'b0;
            flag_inexact <= 1'b0;
        end else begin
            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    flag_invalid <= 1'b0;
                    flag_div_by_zero <= 1'b0;
                    flag_overflow <= 1'b0;
                    flag_underflow <= 1'b0;
                    flag_inexact <= 1'b0;

                    if (enable) begin
                        state <= STATE_UNPACK;
                    end
                end

                STATE_UNPACK: begin
                    // Unpack operand A
                    sign_a = operand_a[79];
                    exp_a = operand_a[78:64];
                    mant_a = operand_a[63:0];
                    detect_special_a;

                    // Unpack operand B
                    sign_b = operand_b[79];
                    exp_b = operand_b[78:64];
                    mant_b = operand_b[63:0];
                    detect_special_b;

                    // Calculate result sign (XOR of signs)
                    result_sign = sign_a ^ sign_b;

                    // Handle special cases
                    if (is_nan_a || is_nan_b) begin
                        // NaN propagation - return canonical NaN
                        result <= {1'b0, 15'h7FFF, 1'b1, 63'h4000000000000000};
                        flag_invalid <= 1'b1;
                        done <= 1'b1;
                        state <= STATE_IDLE;
                    end else if ((is_zero_a && is_zero_b) || (is_inf_a && is_inf_b)) begin
                        // 0÷0 or ∞÷∞ = NaN (invalid operation)
                        result <= {1'b0, 15'h7FFF, 1'b1, 63'h4000000000000000};
                        flag_invalid <= 1'b1;
                        done <= 1'b1;
                        state <= STATE_IDLE;
                    end else if (is_zero_b) begin
                        // x÷0 = ±∞ (divide by zero)
                        result <= {result_sign, 15'h7FFF, 1'b1, 63'd0};
                        flag_div_by_zero <= 1'b1;
                        done <= 1'b1;
                        state <= STATE_IDLE;
                    end else if (is_inf_a) begin
                        // ∞÷finite = ±∞
                        result <= {result_sign, 15'h7FFF, 1'b1, 63'd0};
                        done <= 1'b1;
                        state <= STATE_IDLE;
                    end else if (is_zero_a) begin
                        // 0÷finite = ±0
                        result <= {result_sign, 79'd0};
                        done <= 1'b1;
                        state <= STATE_IDLE;
                    end else if (is_inf_b) begin
                        // finite÷∞ = ±0
                        result <= {result_sign, 79'd0};
                        done <= 1'b1;
                        state <= STATE_IDLE;
                    end else begin
                        state <= STATE_DIVIDE;
                    end
                end

                STATE_DIVIDE: begin
                    // Calculate exponent: exp_a - exp_b + bias
                    // NOTE: Check for underflow/overflow BEFORE calculation
                    if ({1'b0, exp_a} + 17'd16383 < {1'b0, exp_b}) begin
                        // Underflow: exp_a - exp_b + bias < 0
                        result <= {result_sign, 79'd0};
                        flag_underflow <= 1'b1;
                        done <= 1'b1;
                        state <= STATE_IDLE;
                    end else begin
                        // result_exp = exp_a - exp_b + 16383 (using 17-bit signed arithmetic)
                        result_exp = {2'b00, exp_a} - {2'b00, exp_b} + 17'sd16383;

                        // Restoring Division with pre-normalization for mant_a < mant_b
                        divisor = mant_b;
                        quotient = 67'd0;

                        // For mant_a < mant_b: pre-shift by placing mant_a in bits [128:65]
                        // For mant_a >= mant_b: standard placement in bits [127:64]
                        if (mant_a < mant_b) begin
                            remainder = {mant_a, 65'd0};              // mant_a in [128:65], zeros in [64:0]
                            result_exp = result_exp - 17'sd1;         // Compensate exponent
                            pre_shifted = 1'b1;
                            $display("[DIV_DEBUG] Pre-shift: mant_a < mant_b, mant_a in [128:65]=0x%016X",
                                     remainder[128:65]);
                        end else begin
                            remainder = {1'b0, mant_a, 64'd0};        // mant_a in [127:64]
                            pre_shifted = 1'b0;
                        end

                        div_count = 7'd0;
                        remainder_negative = 1'b0;

                        state <= STATE_NORMALIZE;
                    end
                end

                STATE_NORMALIZE: begin
                    // Restoring Division Algorithm (67 iterations for 67-bit quotient)
                    if (div_count < 7'd67) begin
                        if (div_count == 7'd0) begin
                            if (pre_shifted)
                                $display("[DIV_DEBUG] START Restoring (pre-shifted): remainder[128:65]=0x%016X, divisor=0x%016X",
                                         remainder[128:65], divisor);
                            else
                                $display("[DIV_DEBUG] START Restoring Division: remainder[127:64]=0x%016X, divisor=0x%016X",
                                         remainder[127:64], divisor);
                        end

                        // Restoring division: compare appropriate bits with divisor
                        // First iteration of pre-shifted uses [128:65], then shifts to normal [127:64]
                        if (pre_shifted && div_count == 7'd0)
                            do_subtract = (remainder[128:65] >= divisor);
                        else
                            do_subtract = (remainder[127:64] >= divisor);

                        if (do_subtract) begin
                            // Subtract divisor and set quotient bit
                            if (pre_shifted && div_count == 7'd0)
                                remainder[128:65] = remainder[128:65] - divisor;
                            else
                                remainder[127:64] = remainder[127:64] - divisor;
                            quotient[66 - div_count] = 1'b1;
                            if (div_count < 7'd5)
                                $display("[DIV_DEBUG] Iter %0d: HIT, Q[%0d]=1", div_count, 66-div_count);
                        end else begin
                            // Don't subtract, quotient bit stays 0
                            if (div_count < 7'd5)
                                $display("[DIV_DEBUG] Iter %0d: MISS, Q[%0d]=0", div_count, 66-div_count);
                        end

                        // Shift remainder left for next iteration (clears pre_shifted alignment after first iter)
                        remainder = remainder << 1;
                        if (pre_shifted) pre_shifted = 1'b0;  // After first shift, back to normal alignment
                        div_count = div_count + 7'd1;
                    end else begin
                        // Division complete
                        // Division complete
                        result_mant = quotient;
                        $display("[DIV_DEBUG] quotient=0x%017X, bit[66]=%b, bit[65]=%b", quotient, quotient[66], quotient[65]);

                        // Check if normalization is needed
                        // The quotient should have the integer bit at position 66
                        if (result_mant[66]) begin
                            // Already normalized
                            $display("[DIV_DEBUG] Already normalized at bit 66");
                        end else if (result_mant[65]) begin
                            // Need to shift left by 1
                            result_mant = result_mant << 1;
                            result_exp = result_exp - 17'sd1;
                            $display("[DIV_DEBUG] Shifted left by 1, new mant=0x%017X, exp=%0d", result_mant, result_exp);
                        end else begin
                            // Find leading 1 and shift
                            integer i;
                            reg [6:0] shift_amount;
                            shift_amount = 7'd0;

                            for (i = 64; i >= 0; i = i - 1) begin
                                if (result_mant[i] && shift_amount == 7'd0) begin
                                    shift_amount = 7'd66 - i[6:0];
                                end
                            end

                            if (shift_amount > 0 && shift_amount < 67) begin
                                result_mant = result_mant << shift_amount;
                                result_exp = result_exp - shift_amount;
                                $display("[DIV_DEBUG] Shifted left by %0d, new mant=0x%017X, exp=%0d", shift_amount, result_mant, result_exp);
                            end
                        end

                        // Check for overflow/underflow after normalization
                        // Check overflow FIRST to avoid misdetecting wrapped underflow
                        if (result_exp > 17'sd32766) begin
                            // Overflow
                            result <= {result_sign, 15'h7FFF, 1'b1, 63'd0}; // ±∞
                            flag_overflow <= 1'b1;
                            done <= 1'b1;
                            state <= STATE_IDLE;
                        end else if (result_exp < 17'sd1) begin
                            // Underflow
                            result <= {result_sign, 79'd0};
                            flag_underflow <= 1'b1;
                            done <= 1'b1;
                            state <= STATE_IDLE;
                        end else begin
                            state <= STATE_ROUND;
                        end
                    end
                end

                STATE_ROUND: begin
                    // Extract guard, round, sticky bits from result_mant
                    // After normalization, integer bit is at position 66
                    // Bits 65:3 are fraction, bits 2:1:0 are guard/round/sticky
                    round_bit = result_mant[1];
                    sticky_bit = result_mant[0];

                    // Round according to mode
                    case (rounding_mode)
                        2'b00: begin // Round to nearest (ties to even)
                            if (round_bit && (sticky_bit || result_mant[2])) begin
                                result_mant = (result_mant >> 3) + 65'd1;
                                flag_inexact <= 1'b1;
                            end else begin
                                result_mant = result_mant >> 3;
                                if (round_bit || sticky_bit) flag_inexact <= 1'b1;
                            end
                        end
                        2'b01: begin // Round down (toward -∞)
                            if (result_sign && (round_bit || sticky_bit)) begin
                                result_mant = (result_mant >> 3) + 65'd1;
                                flag_inexact <= 1'b1;
                            end else begin
                                result_mant = result_mant >> 3;
                                if (round_bit || sticky_bit) flag_inexact <= 1'b1;
                            end
                        end
                        2'b10: begin // Round up (toward +∞)
                            if (!result_sign && (round_bit || sticky_bit)) begin
                                result_mant = (result_mant >> 3) + 65'd1;
                                flag_inexact <= 1'b1;
                            end else begin
                                result_mant = result_mant >> 3;
                                if (round_bit || sticky_bit) flag_inexact <= 1'b1;
                            end
                        end
                        2'b11: begin // Round toward zero (truncate)
                            result_mant = result_mant >> 3;
                            if (round_bit || sticky_bit) flag_inexact <= 1'b1;
                        end
                    endcase

                    // Check for rounding overflow
                    if (result_mant[64]) begin
                        result_mant = result_mant >> 1;
                        result_exp = result_exp + 17'sd1;

                        if (result_exp > 17'sd32766) begin
                            result <= {result_sign, 15'h7FFF, 1'b1, 63'd0};
                            flag_overflow <= 1'b1;
                            done <= 1'b1;
                            state <= STATE_IDLE;
                        end else begin
                            state <= STATE_PACK;
                        end
                    end else begin
                        state <= STATE_PACK;
                    end
                end

                STATE_PACK: begin
                    // Pack result
                    $display("[DIV_DEBUG] PACK: sign=%b, exp=0x%04X, mant[63:0]=0x%016X, mant[66:64]=0b%03b",
                             result_sign, result_exp[14:0], result_mant[63:0], result_mant[66:64]);
                    result <= {result_sign, result_exp[14:0], result_mant[63:0]};
                    done <= 1'b1;
                    state <= STATE_IDLE;
                end

                default: begin
                    state <= STATE_IDLE;
                end
            endcase
        end
    end

endmodule
