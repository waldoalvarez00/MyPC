// Copyright 2025, Waldo Alvarez, https://pipflow.com
// License GPL 2.0

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
    output reg error,
    output reg flag_inexact,  // Inexact result (from rounding)

    //=================================================================
    // STRATEGY 1: Shared Arithmetic Unit Interface
    // Request interface to share AddSub and MulDiv units
    //=================================================================
    output reg        ext_addsub_req,      // AddSub request
    output reg [79:0] ext_addsub_a,        // AddSub operand A
    output reg [79:0] ext_addsub_b,        // AddSub operand B
    output reg        ext_addsub_sub,      // AddSub subtract flag
    input wire [79:0] ext_addsub_result,   // AddSub result
    input wire        ext_addsub_done,     // AddSub done
    input wire        ext_addsub_invalid,  // AddSub exception flags
    input wire        ext_addsub_overflow,
    input wire        ext_addsub_underflow,
    input wire        ext_addsub_inexact,

    output reg        ext_muldiv_req,      // MulDiv request
    output reg        ext_muldiv_op,       // MulDiv operation (0=mul, 1=div)
    output reg [79:0] ext_muldiv_a,        // MulDiv operand A
    output reg [79:0] ext_muldiv_b,        // MulDiv operand B
    input wire [79:0] ext_muldiv_result,   // MulDiv result
    input wire        ext_muldiv_done,     // MulDiv done
    input wire        ext_muldiv_invalid,  // MulDiv exception flags
    input wire        ext_muldiv_div_by_zero,
    input wire        ext_muldiv_overflow,
    input wire        ext_muldiv_underflow,
    input wire        ext_muldiv_inexact,

    //=================================================================
    // STRATEGY 2D: Shared Arithmetic Unit Interface for Polynomial Evaluator
    // These signals are passed through to the internal polynomial evaluator
    //=================================================================
    output wire        ext_poly_addsub_req,      // Polynomial AddSub request
    output wire [79:0] ext_poly_addsub_a,        // Polynomial AddSub operand A
    output wire [79:0] ext_poly_addsub_b,        // Polynomial AddSub operand B
    input wire [79:0] ext_poly_addsub_result,   // Polynomial AddSub result
    input wire        ext_poly_addsub_done,     // Polynomial AddSub done
    input wire        ext_poly_addsub_invalid,  // Polynomial AddSub exception flags
    input wire        ext_poly_addsub_overflow,
    input wire        ext_poly_addsub_underflow,
    input wire        ext_poly_addsub_inexact,

    output wire        ext_poly_muldiv_req,      // Polynomial MulDiv request
    output wire [79:0] ext_poly_muldiv_a,        // Polynomial MulDiv operand A
    output wire [79:0] ext_poly_muldiv_b,        // Polynomial MulDiv operand B
    input wire [79:0] ext_poly_muldiv_result,   // Polynomial MulDiv result
    input wire        ext_poly_muldiv_done,     // Polynomial MulDiv done
    input wire        ext_poly_muldiv_invalid,  // Polynomial MulDiv exception flags
    input wire        ext_poly_muldiv_overflow,
    input wire        ext_poly_muldiv_underflow,
    input wire        ext_poly_muldiv_inexact
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

    localparam FP80_ZERO    = 80'h0000_0000000000000000;
    localparam FP80_ONE     = 80'h3FFF_8000000000000000;
    localparam FP80_NEG_INF = 80'hFFFF_8000000000000000;  // -Infinity
    localparam FP80_POS_INF = 80'h7FFF_8000000000000000;  // +Infinity
    localparam FP80_QNAN    = 80'h7FFF_C000000000000000;  // Quiet NaN

    //=================================================================
    // Helper Functions for Special Value Detection
    //=================================================================

    // Check if FP80 value is zero (positive or negative)
    function automatic is_zero;
        input [79:0] val;
        begin
            is_zero = (val[78:0] == 79'd0);  // All bits except sign are zero
        end
    endfunction

    // Check if FP80 value is negative (sign bit = 1)
    function automatic is_negative;
        input [79:0] val;
        begin
            is_negative = val[79];
        end
    endfunction

    // Check if FP80 value is a NaN
    function automatic is_nan;
        input [79:0] val;
        begin
            is_nan = (val[78:64] == 15'h7FFF) && (val[62:0] != 63'd0);
        end
    endfunction

    // Check if FP80 value is infinity
    function automatic is_infinity;
        input [79:0] val;
        begin
            is_infinity = (val[78:64] == 15'h7FFF) && (val[62:0] == 63'd0);
        end
    endfunction

    // Check if |FP80 value| >= 1.0 (for F2XM1 domain checking)
    // 1.0 has exponent 0x3FFF (bias of 16383)
    function automatic is_abs_ge_one;
        input [79:0] val;
        begin
            is_abs_ge_one = (val[78:64] >= 15'h3FFF);
        end
    endfunction

    //=================================================================
    // Module Instantiations
    //=================================================================

    // CORDIC Wrapper (for sin/cos/tan/atan)
    reg cordic_enable;
    reg [1:0] cordic_mode;  // 00=rotation (sin/cos), 01=vectoring (atan), 10=tan
    wire [79:0] cordic_sin_out, cordic_cos_out;
    wire [79:0] cordic_atan_out, cordic_magnitude_out, cordic_tan_out;
    wire cordic_done, cordic_error;

    // CORDIC shared arithmetic unit interface
    wire        cordic_addsub_req;
    wire [79:0] cordic_addsub_a, cordic_addsub_b;
    wire        cordic_addsub_sub;
    wire [79:0] cordic_addsub_result;
    wire        cordic_addsub_done, cordic_addsub_invalid;

    wire        cordic_muldiv_req;
    wire        cordic_muldiv_op;
    wire [79:0] cordic_muldiv_a, cordic_muldiv_b;
    wire [79:0] cordic_muldiv_result;
    wire        cordic_muldiv_done, cordic_muldiv_invalid;

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
        .tan_out(cordic_tan_out),
        .done(cordic_done),
        .error(cordic_error),

        // Plan 2: Shared arithmetic unit interface
        .ext_addsub_req(cordic_addsub_req),
        .ext_addsub_a(cordic_addsub_a),
        .ext_addsub_b(cordic_addsub_b),
        .ext_addsub_sub(cordic_addsub_sub),
        .ext_addsub_result(cordic_addsub_result),
        .ext_addsub_done(cordic_addsub_done),
        .ext_addsub_invalid(cordic_addsub_invalid),

        .ext_muldiv_req(cordic_muldiv_req),
        .ext_muldiv_op(cordic_muldiv_op),
        .ext_muldiv_a(cordic_muldiv_a),
        .ext_muldiv_b(cordic_muldiv_b),
        .ext_muldiv_result(cordic_muldiv_result),
        .ext_muldiv_done(cordic_muldiv_done),
        .ext_muldiv_invalid(cordic_muldiv_invalid)
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
        .error(poly_error),

        // Strategy 2D: Shared AddSub unit interface
        .ext_addsub_req(ext_poly_addsub_req),
        .ext_addsub_a(ext_poly_addsub_a),
        .ext_addsub_b(ext_poly_addsub_b),
        .ext_addsub_result(ext_poly_addsub_result),
        .ext_addsub_done(ext_poly_addsub_done),
        .ext_addsub_invalid(ext_poly_addsub_invalid),
        .ext_addsub_overflow(ext_poly_addsub_overflow),
        .ext_addsub_underflow(ext_poly_addsub_underflow),
        .ext_addsub_inexact(ext_poly_addsub_inexact),

        // Strategy 2D: Shared MulDiv unit interface
        .ext_muldiv_req(ext_poly_muldiv_req),
        .ext_muldiv_a(ext_poly_muldiv_a),
        .ext_muldiv_b(ext_poly_muldiv_b),
        .ext_muldiv_result(ext_poly_muldiv_result),
        .ext_muldiv_done(ext_poly_muldiv_done),
        .ext_muldiv_invalid(ext_poly_muldiv_invalid),
        .ext_muldiv_overflow(ext_poly_muldiv_overflow),
        .ext_muldiv_underflow(ext_poly_muldiv_underflow),
        .ext_muldiv_inexact(ext_poly_muldiv_inexact)
    );

    // Newton-Raphson Square Root - REMOVED (handled in microcode)
    // SQRT operations are handled by the microsequencer at address 0x0140
    // This eliminates ~22K area (22% reduction) with only 0.6% performance penalty

    // Stub signals for compatibility
    reg sqrt_enable;
    wire sqrt_done = sqrt_enable;  // Immediate completion (unsupported in hardware)
    wire sqrt_error = 1'b0;         // No error, just not supported in hardware
    wire [79:0] sqrt_out = 80'h7FFF_C000000000000000;  // Return NaN to indicate microcode needed

    //=================================================================
    // STRATEGY 1: Shared Arithmetic Units
    // REMOVED: Duplicate Division, Multiplication, and AddSub units
    // Now using shared units from FPU_ArithmeticUnit via external interface
    //
    // Area Savings:
    // - Division Unit:       ~15,000 gates REMOVED
    // - Multiplication Unit: ~12,000 gates REMOVED
    // - AddSub Unit:         ~8,000 gates REMOVED
    // - Control overhead:    +2,000 gates ADDED
    // NET SAVINGS:           ~33,000 gates (19% of total FPU area)
    //
    // Performance Impact:
    // - FPTAN:    +60 cycles (+17%)
    // - FYL2X:    +25 cycles (+17%)
    // - FYL2XP1:  +35 cycles (+23%)
    // - Average:  ~6% slower (only 3 operations affected)
    //=================================================================

    // Removed duplicate instantiations (lines 143-207 in original):
    // - FPU_IEEE754_Divide div_unit
    // - FPU_IEEE754_Multiply mul_unit
    // - FPU_IEEE754_AddSub addsub_unit

    // These operations now route through ext_addsub_req and ext_muldiv_req interfaces

    //=================================================================
    // Arithmetic Unit Arbiter (Plan 2 CORDIC Integration)
    //
    // Priority (highest to lowest):
    // 1. Direct FPU_Transcendental requests (state machine driven)
    // 2. CORDIC correction requests
    // 3. Polynomial evaluator requests
    //
    // This ensures FPTAN division and FYL2X multiply have priority
    //=================================================================

    // Internal request signals from state machine
    reg        local_addsub_req;
    reg [79:0] local_addsub_a, local_addsub_b;
    reg        local_addsub_sub;

    reg        local_muldiv_req;
    reg        local_muldiv_op;
    reg [79:0] local_muldiv_a, local_muldiv_b;

    // Arbitrated result routing - grants persist until done
    reg [1:0]  addsub_grant;  // 00=none, 01=local, 10=cordic, 11=poly
    reg [1:0]  muldiv_grant;  // 00=none, 01=local, 10=cordic, 11=poly

    // AddSub Arbiter - combinational request routing
    always @(*) begin
        if (local_addsub_req) begin
            ext_addsub_req = 1'b1;
            ext_addsub_a = local_addsub_a;
            ext_addsub_b = local_addsub_b;
            ext_addsub_sub = local_addsub_sub;
        end else if (cordic_addsub_req) begin
            ext_addsub_req = 1'b1;
            ext_addsub_a = cordic_addsub_a;
            ext_addsub_b = cordic_addsub_b;
            ext_addsub_sub = cordic_addsub_sub;
        end else if (ext_poly_addsub_req) begin
            ext_addsub_req = 1'b1;
            ext_addsub_a = ext_poly_addsub_a;
            ext_addsub_b = ext_poly_addsub_b;
            ext_addsub_sub = 1'b0;
        end else begin
            ext_addsub_req = 1'b0;
            ext_addsub_a = FP80_ZERO;
            ext_addsub_b = FP80_ZERO;
            ext_addsub_sub = 1'b0;
        end
    end

    // AddSub Grant - registered, persists until done
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            addsub_grant <= 2'd0;
        end else begin
            if (ext_addsub_done) begin
                // Clear grant when done received
                addsub_grant <= 2'd0;
            end else if (addsub_grant == 2'd0) begin
                // Capture new grant when idle
                if (local_addsub_req)
                    addsub_grant <= 2'd1;
                else if (cordic_addsub_req)
                    addsub_grant <= 2'd2;
                else if (ext_poly_addsub_req)
                    addsub_grant <= 2'd3;
            end
            // Otherwise keep current grant
        end
    end

    // MulDiv Arbiter - combinational request routing
    always @(*) begin
        if (local_muldiv_req) begin
            ext_muldiv_req = 1'b1;
            ext_muldiv_op = local_muldiv_op;
            ext_muldiv_a = local_muldiv_a;
            ext_muldiv_b = local_muldiv_b;
        end else if (cordic_muldiv_req) begin
            ext_muldiv_req = 1'b1;
            ext_muldiv_op = cordic_muldiv_op;
            ext_muldiv_a = cordic_muldiv_a;
            ext_muldiv_b = cordic_muldiv_b;
        end else if (ext_poly_muldiv_req) begin
            ext_muldiv_req = 1'b1;
            ext_muldiv_op = 1'b0;
            ext_muldiv_a = ext_poly_muldiv_a;
            ext_muldiv_b = ext_poly_muldiv_b;
        end else begin
            ext_muldiv_req = 1'b0;
            ext_muldiv_op = 1'b0;
            ext_muldiv_a = FP80_ZERO;
            ext_muldiv_b = FP80_ZERO;
        end
    end

    // MulDiv Grant - registered, persists until done
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            muldiv_grant <= 2'd0;
        end else begin
            if (ext_muldiv_done) begin
                // Clear grant when done received
                muldiv_grant <= 2'd0;
            end else if (muldiv_grant == 2'd0) begin
                // Capture new grant when idle
                if (local_muldiv_req)
                    muldiv_grant <= 2'd1;
                else if (cordic_muldiv_req)
                    muldiv_grant <= 2'd2;
                else if (ext_poly_muldiv_req)
                    muldiv_grant <= 2'd3;
            end
            // Otherwise keep current grant
        end
    end

    // Result Routing (combinational)
    // Route results back to the appropriate requestor based on grant
    assign cordic_addsub_result = (addsub_grant == 2'd2) ? ext_addsub_result : FP80_ZERO;
    assign cordic_addsub_done   = (addsub_grant == 2'd2) ? ext_addsub_done : 1'b0;
    assign cordic_addsub_invalid = (addsub_grant == 2'd2) ? ext_addsub_invalid : 1'b0;

    assign cordic_muldiv_result = (muldiv_grant == 2'd2) ? ext_muldiv_result : FP80_ZERO;
    assign cordic_muldiv_done   = (muldiv_grant == 2'd2) ? ext_muldiv_done : 1'b0;
    assign cordic_muldiv_invalid = (muldiv_grant == 2'd2) ? ext_muldiv_invalid : 1'b0;

    // Polynomial results are passed directly through module ports (ext_poly_*)
    // Local results are captured in state machine

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
            flag_inexact <= 1'b0;
            result_primary <= FP80_ZERO;
            result_secondary <= FP80_ZERO;
            has_secondary <= 1'b0;
            cordic_enable <= 1'b0;
            cordic_mode <= 2'b00;
            poly_enable <= 1'b0;
            poly_select <= 4'd0;
            poly_input <= FP80_ZERO;
            sqrt_enable <= 1'b0;

            // Local arbiter request signals
            local_addsub_req <= 1'b0;
            local_addsub_a <= FP80_ZERO;
            local_addsub_b <= FP80_ZERO;
            local_addsub_sub <= 1'b0;
            local_muldiv_req <= 1'b0;
            local_muldiv_op <= 1'b0;
            local_muldiv_a <= FP80_ZERO;
            local_muldiv_b <= FP80_ZERO;

            current_operation <= 4'd0;
        end else begin
            // Debug: show state when enable arrives
            `ifdef ICARUS
            if (enable && state != STATE_IDLE) begin
                $display("[TRANS WARN] enable=1 but state=%0d (not IDLE!)", state);
            end
            `endif

            // Accumulate inexact flag from internal arithmetic operations
            // This captures inexact from any internal operation during the transcendental computation
            if (state != STATE_IDLE && state != STATE_DONE) begin
                // Check if any internal operation completed with inexact result
                if (ext_addsub_done && ext_addsub_inexact)
                    flag_inexact <= 1'b1;
                if (ext_muldiv_done && ext_muldiv_inexact)
                    flag_inexact <= 1'b1;
                if (ext_poly_addsub_done && ext_poly_addsub_inexact)
                    flag_inexact <= 1'b1;
                if (ext_poly_muldiv_done && ext_poly_muldiv_inexact)
                    flag_inexact <= 1'b1;
            end

            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    // Don't clear error here - preserve it for FPU_Core to sample
                    // Error will be cleared when a new operation starts
                    flag_inexact <= 1'b0;
                    has_secondary <= 1'b0;
                    cordic_enable <= 1'b0;
                    poly_enable <= 1'b0;
                    sqrt_enable <= 1'b0;

                    // Clear local arbiter requests
                    local_addsub_req <= 1'b0;
                    local_muldiv_req <= 1'b0;

                    if (enable) begin
                        error <= 1'b0;  // Clear error only at start of new operation
                        `ifdef ICARUS
                        $display("[TRANS] STATE_IDLE: enable=1, op=%0d, A=%h B=%h", operation, operand_a, operand_b);
                        `endif
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
                            cordic_mode <= 2'b00;  // Rotation mode (SIN/COS)
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_COS: begin
                            // Cosine via CORDIC rotation mode
                            cordic_enable <= 1'b1;
                            cordic_mode <= 2'b00;  // Rotation mode (SIN/COS)
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_SINCOS: begin
                            // Both sin and cos via CORDIC rotation mode
                            cordic_enable <= 1'b1;
                            cordic_mode <= 2'b00;  // Rotation mode (SIN/COS)
                            has_secondary <= 1'b1;  // Will return both results
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_TAN: begin
                            // Tangent via CORDIC Plan 2: 16 iterations + correction
                            cordic_enable <= 1'b1;
                            cordic_mode <= 2'b10;  // TAN mode (16-iter with polynomial correction)
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_ATAN: begin
                            // Arctangent via CORDIC vectoring mode + correction
                            cordic_enable <= 1'b1;
                            cordic_mode <= 2'b01;  // Vectoring mode (ATAN with correction)
                            state <= STATE_WAIT_CORDIC;
                        end

                        OP_F2XM1: begin
                            // 2^x - 1 via polynomial approximation
                            // Valid domain: -1 <= x <= 1
                            `ifdef ICARUS
                            $display("[TRANS F2XM1] A=%h is_nan=%b is_abs_ge_one=%b",
                                operand_a, is_nan(operand_a), is_abs_ge_one(operand_a));
                            `endif
                            if (is_nan(operand_a)) begin
                                // NaN propagation
                                `ifdef ICARUS
                                $display("[TRANS F2XM1] NaN detected -> STATE_DONE");
                                `endif
                                result_primary <= FP80_QNAN;
                                error <= 1'b1;
                                state <= STATE_DONE;
                            end else if (is_abs_ge_one(operand_a)) begin
                                // Domain error: |x| >= 1
                                `ifdef ICARUS
                                $display("[TRANS F2XM1] |x| >= 1 detected -> STATE_DONE (domain error)");
                                `endif
                                result_primary <= FP80_QNAN;
                                error <= 1'b1;
                                state <= STATE_DONE;
                            end else begin
                                // Valid input, use polynomial approximation
                                poly_enable <= 1'b1;
                                poly_select <= 4'd0;  // F2XM1 polynomial
                                poly_input <= operand_a;
                                state <= STATE_WAIT_POLY;
                            end
                        end

                        OP_FYL2X: begin
                            // y × log₂(x): First check for special cases
                            // operand_a = x, operand_b = y
                            `ifdef ICARUS
                            $display("[TRANS FYL2X] A=%h B=%h is_zero_a=%b is_neg_a=%b is_nan_a=%b",
                                operand_a, operand_b, is_zero(operand_a),
                                is_negative(operand_a), is_nan(operand_a));
                            `endif
                            if (is_nan(operand_a) || is_nan(operand_b)) begin
                                // NaN propagation
                                `ifdef ICARUS
                                $display("[TRANS FYL2X] NaN detected -> STATE_DONE");
                                `endif
                                result_primary <= FP80_QNAN;
                                error <= 1'b1;
                                state <= STATE_DONE;
                            end else if (is_zero(operand_a)) begin
                                // log₂(0) = -∞
                                // Result = y × -∞
                                `ifdef ICARUS
                                $display("[TRANS FYL2X] x=0 detected -> STATE_DONE");
                                `endif
                                if (is_zero(operand_b)) begin
                                    // 0 × -∞ is undefined
                                    result_primary <= FP80_QNAN;
                                    error <= 1'b1;
                                end else if (is_negative(operand_b)) begin
                                    // negative × -∞ = +∞
                                    result_primary <= FP80_POS_INF;
                                end else begin
                                    // positive × -∞ = -∞
                                    result_primary <= FP80_NEG_INF;
                                end
                                state <= STATE_DONE;
                            end else if (is_negative(operand_a) && !is_zero(operand_a)) begin
                                // log₂(negative) is undefined
                                `ifdef ICARUS
                                $display("[TRANS FYL2X] x<0 detected -> STATE_DONE");
                                `endif
                                result_primary <= FP80_QNAN;
                                error <= 1'b1;
                                state <= STATE_DONE;
                            end else begin
                                // Normal case: compute log₂(x)
                                `ifdef ICARUS
                                $display("[TRANS FYL2X] Normal case -> poly eval");
                                `endif
                                poly_enable <= 1'b1;
                                poly_select <= 4'd1;  // LOG2 polynomial
                                poly_input <= operand_a;
                                state <= STATE_WAIT_POLY;
                            end
                        end

                        OP_FYL2XP1: begin
                            // y × log₂(x+1): First add 1 to x using shared AddSub unit
                            local_addsub_req <= 1'b1;
                            local_addsub_a <= operand_a;  // x
                            local_addsub_b <= FP80_ONE;   // 1.0
                            local_addsub_sub <= 1'b0;     // Add (not subtract)
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
                                    // Direct TAN output from CORDIC Plan 2 (16-iter + correction)
                                    result_primary <= cordic_tan_out;
                                    // Note: Also push 1.0 per Intel 8087 spec (for FPTAN compatibility)
                                    result_secondary <= FP80_ONE;
                                    has_secondary <= 1'b1;
                                    state <= STATE_DONE;
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
                            // FYL2X and FYL2XP1 need multiplication by y using shared MulDiv unit
                            if (current_operation == OP_FYL2X ||
                                current_operation == OP_FYL2XP1) begin
                                // Multiply log result by operand_b (y)
                                local_muldiv_req <= 1'b1;
                                local_muldiv_op <= 1'b0;  // 0 = multiply
                                local_muldiv_a <= poly_result;  // log₂(x) or log₂(x+1)
                                local_muldiv_b <= operand_b;    // y
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
                    // Wait for addition to complete (FYL2XP1: x+1) using shared AddSub unit
                    local_addsub_req <= 1'b0;  // Clear request after it's accepted
                    if (ext_addsub_done && addsub_grant == 2'd1) begin  // Check we got the grant
                        if (ext_addsub_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            // Now compute log₂(x+1) using the add result
                            poly_enable <= 1'b1;
                            poly_select <= 4'd1;  // LOG2 polynomial
                            poly_input <= ext_addsub_result;  // Pass (x+1) to polynomial
                            state <= STATE_WAIT_POLY;
                        end
                    end
                end

                STATE_WAIT_DIV: begin
                    // Wait for division to complete (UNUSED after Plan 2 - TAN now direct)
                    // Kept for compatibility with potential future uses
                    local_muldiv_req <= 1'b0;  // Clear request after it's accepted
                    if (ext_muldiv_done && muldiv_grant == 2'd1) begin  // Check we got the grant
                        if (ext_muldiv_invalid || ext_muldiv_div_by_zero) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            result_primary <= ext_muldiv_result;
                            state <= STATE_DONE;
                        end
                    end
                end

                STATE_WAIT_MUL: begin
                    // Wait for multiplication to complete (FYL2X, FYL2XP1: log*y) using shared MulDiv unit
                    local_muldiv_req <= 1'b0;  // Clear request after it's accepted
                    if (ext_muldiv_done && muldiv_grant == 2'd1) begin  // Check we got the grant
                        if (ext_muldiv_invalid) begin
                            error <= 1'b1;
                            state <= STATE_DONE;
                        end else begin
                            result_primary <= ext_muldiv_result;  // y × log₂(x) or y × log₂(x+1)
                            state <= STATE_DONE;
                        end
                    end
                end

                STATE_DONE: begin
                    done <= 1'b1;
                    // Wait for enable to go low before returning to IDLE
                    // This ensures proper handshaking with the microsequencer
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
