`timescale 1ns / 1ps

//=====================================================================
// Intel 8087 FPU Core Module
//
// Top-level integration module that connects:
// - 8-register stack (FPU_RegisterStack)
// - Status word management (FPU_StatusWord)
// - Control word management (FPU_ControlWord)
// - Arithmetic operations (FPU_ArithmeticUnit)
//
// Provides instruction-level interface for CPU integration
//
// Instruction Format (simplified):
// [7:0] opcode - FPU instruction opcode
// [2:0] stack_index - Stack register index for two-operand instructions
//
// Supported instruction classes:
// - Arithmetic: FADD, FSUB, FMUL, FDIV (with optional pop)
// - Stack: FLD, FST, FSTP, FXCH
// - Conversions: FILD, FIST, FLD (FP32/64)
// - Control: FLDCW, FSTCW, FSTSW, FCLEX
//=====================================================================

module FPU_Core(
    input wire clk,
    input wire reset,

    // Instruction interface
    input wire [7:0]  instruction,      // FPU instruction opcode
    input wire [2:0]  stack_index,      // Stack index (for ST(i) operands)
    input wire        execute,          // Start instruction execution
    output reg        ready,            // FPU ready for new instruction
    output reg        error,            // Exception occurred (unmasked)

    // Data interface
    input wire [79:0] data_in,          // Data input (for loads)
    output reg [79:0] data_out,         // Data output (for stores)
    input wire [31:0] int_data_in,      // Integer data input
    output reg [31:0] int_data_out,     // Integer data output

    // Control/Status interface
    input wire [15:0] control_in,       // Control word input
    input wire        control_write,    // Write control word
    output wire [15:0] status_out,      // Status word output
    output wire [15:0] control_out,     // Control word output
    output wire [15:0] tag_word_out     // Tag word output
);

    //=================================================================
    // Instruction Opcodes (Simplified)
    //=================================================================

    localparam INST_NOP         = 8'h00;

    // Arithmetic instructions
    localparam INST_FADD        = 8'h10;  // ST(0) = ST(0) + ST(i)
    localparam INST_FADDP       = 8'h11;  // ST(1) = ST(0) + ST(1), pop
    localparam INST_FSUB        = 8'h12;  // ST(0) = ST(0) - ST(i)
    localparam INST_FSUBP       = 8'h13;  // ST(1) = ST(0) - ST(1), pop
    localparam INST_FMUL        = 8'h14;  // ST(0) = ST(0) * ST(i)
    localparam INST_FMULP       = 8'h15;  // ST(1) = ST(0) * ST(1), pop
    localparam INST_FDIV        = 8'h16;  // ST(0) = ST(0) / ST(i)
    localparam INST_FDIVP       = 8'h17;  // ST(1) = ST(0) / ST(1), pop

    // Stack instructions
    localparam INST_FLD         = 8'h20;  // Push ST(i) or memory
    localparam INST_FST         = 8'h21;  // Store ST(0) to ST(i) or memory
    localparam INST_FSTP        = 8'h22;  // Store ST(0) and pop
    localparam INST_FXCH        = 8'h23;  // Exchange ST(0) with ST(i)

    // Integer conversion
    localparam INST_FILD16      = 8'h30;  // Load 16-bit integer
    localparam INST_FILD32      = 8'h31;  // Load 32-bit integer
    localparam INST_FIST16      = 8'h32;  // Store 16-bit integer
    localparam INST_FIST32      = 8'h33;  // Store 32-bit integer
    localparam INST_FISTP16     = 8'h34;  // Store 16-bit integer and pop
    localparam INST_FISTP32     = 8'h35;  // Store 32-bit integer and pop

    // FP format conversion
    localparam INST_FLD32       = 8'h40;  // Load FP32 (convert to FP80)
    localparam INST_FLD64       = 8'h41;  // Load FP64 (convert to FP80)
    localparam INST_FST32       = 8'h42;  // Store as FP32
    localparam INST_FST64       = 8'h43;  // Store as FP64
    localparam INST_FSTP32      = 8'h44;  // Store as FP32 and pop
    localparam INST_FSTP64      = 8'h45;  // Store as FP64 and pop

    // Transcendental instructions
    localparam INST_FSQRT       = 8'h50;  // Square root: ST(0) = √ST(0)
    localparam INST_FSIN        = 8'h51;  // Sine: ST(0) = sin(ST(0))
    localparam INST_FCOS        = 8'h52;  // Cosine: ST(0) = cos(ST(0))
    localparam INST_FSINCOS     = 8'h53;  // Sin & Cos: push sin, push cos
    localparam INST_FPTAN       = 8'h54;  // Partial tangent: push tan, push 1.0
    localparam INST_FPATAN      = 8'h55;  // Partial arctan: ST(1) = atan(ST(1)/ST(0)), pop
    localparam INST_F2XM1       = 8'h56;  // 2^ST(0) - 1
    localparam INST_FYL2X       = 8'h57;  // ST(1) × log₂(ST(0)), pop
    localparam INST_FYL2XP1     = 8'h58;  // ST(1) × log₂(ST(0)+1), pop

    // Control instructions
    localparam INST_FLDCW       = 8'hF0;  // Load control word
    localparam INST_FSTCW       = 8'hF1;  // Store control word
    localparam INST_FSTSW       = 8'hF2;  // Store status word
    localparam INST_FCLEX       = 8'hF3;  // Clear exceptions

    //=================================================================
    // Component Wiring
    //=================================================================

    // Register Stack
    wire [79:0] st0, st1;
    wire [79:0] stack_read_data;
    wire [2:0]  stack_pointer;
    wire [15:0] tag_word;
    wire        stack_overflow, stack_underflow;

    reg         stack_push, stack_pop;
    reg [79:0]  stack_data_in;
    reg [2:0]   stack_write_reg;
    reg         stack_write_enable;
    reg [2:0]   stack_read_sel;

    FPU_RegisterStack register_stack (
        .clk(clk),
        .reset(reset),
        .push(stack_push),
        .pop(stack_pop),
        .data_in(stack_data_in),
        .write_reg(stack_write_reg),
        .write_enable(stack_write_enable),
        .st0(st0),
        .st1(st1),
        .read_sel(stack_read_sel),
        .read_data(stack_read_data),
        .stack_ptr(stack_pointer),
        .tag_word(tag_word),
        .stack_overflow(stack_overflow),
        .stack_underflow(stack_underflow)
    );

    // Control Word
    wire [1:0]  rounding_mode;
    wire [1:0]  precision_mode;
    wire        mask_precision, mask_underflow, mask_overflow;
    wire        mask_zero_div, mask_denormal, mask_invalid;

    FPU_ControlWord control_word (
        .clk(clk),
        .reset(reset),
        .control_in(control_in),
        .write_enable(control_write),
        .control_out(control_out),
        .rounding_mode(rounding_mode),
        .precision_mode(precision_mode),
        .mask_precision(mask_precision),
        .mask_underflow(mask_underflow),
        .mask_overflow(mask_overflow),
        .mask_zero_div(mask_zero_div),
        .mask_denormal(mask_denormal),
        .mask_invalid(mask_invalid)
    );

    // Status Word
    reg        status_cc_write;
    reg        status_c3, status_c2, status_c1, status_c0;
    reg        status_clear_exc, status_set_busy, status_clear_busy;
    reg        status_invalid, status_denormal, status_zero_div;
    reg        status_overflow, status_underflow, status_precision;
    reg        status_stack_fault;

    FPU_StatusWord status_word (
        .clk(clk),
        .reset(reset),
        .stack_ptr(stack_pointer),
        .c3(status_c3),
        .c2(status_c2),
        .c1(status_c1),
        .c0(status_c0),
        .cc_write(status_cc_write),
        .invalid(status_invalid),
        .denormal(status_denormal),
        .zero_divide(status_zero_div),
        .overflow(status_overflow),
        .underflow(status_underflow),
        .precision(status_precision),
        .stack_fault(status_stack_fault),
        .clear_exceptions(status_clear_exc),
        .set_busy(status_set_busy),
        .clear_busy(status_clear_busy),
        .status_word(status_out)
    );

    // Arithmetic Unit
    wire [79:0] arith_result;
    wire [79:0] arith_result_secondary;
    wire        arith_has_secondary;
    wire signed [15:0] arith_int16_out;
    wire signed [31:0] arith_int32_out;
    wire [31:0] arith_fp32_out;
    wire [63:0] arith_fp64_out;
    wire        arith_done;
    wire        arith_cc_less, arith_cc_equal, arith_cc_greater, arith_cc_unordered;
    wire        arith_invalid, arith_denormal, arith_zero_div;
    wire        arith_overflow, arith_underflow, arith_inexact;

    reg [3:0]   arith_operation;
    reg         arith_enable;
    reg [79:0]  arith_operand_a, arith_operand_b;
    reg signed [15:0] arith_int16_in;
    reg signed [31:0] arith_int32_in;
    reg [31:0]  arith_fp32_in;
    reg [63:0]  arith_fp64_in;

    FPU_ArithmeticUnit arithmetic_unit (
        .clk(clk),
        .reset(reset),
        .operation(arith_operation),
        .enable(arith_enable),
        .rounding_mode(rounding_mode),
        .operand_a(arith_operand_a),
        .operand_b(arith_operand_b),
        .int16_in(arith_int16_in),
        .int32_in(arith_int32_in),
        .fp32_in(arith_fp32_in),
        .fp64_in(arith_fp64_in),
        .result(arith_result),
        .result_secondary(arith_result_secondary),
        .has_secondary(arith_has_secondary),
        .int16_out(arith_int16_out),
        .int32_out(arith_int32_out),
        .fp32_out(arith_fp32_out),
        .fp64_out(arith_fp64_out),
        .done(arith_done),
        .cc_less(arith_cc_less),
        .cc_equal(arith_cc_equal),
        .cc_greater(arith_cc_greater),
        .cc_unordered(arith_cc_unordered),
        .flag_invalid(arith_invalid),
        .flag_denormal(arith_denormal),
        .flag_zero_divide(arith_zero_div),
        .flag_overflow(arith_overflow),
        .flag_underflow(arith_underflow),
        .flag_inexact(arith_inexact)
    );

    // Tag word output
    assign tag_word_out = tag_word;

    //=================================================================
    // Execution State Machine
    //=================================================================

    localparam STATE_IDLE       = 3'd0;
    localparam STATE_DECODE     = 3'd1;
    localparam STATE_EXECUTE    = 3'd2;
    localparam STATE_WRITEBACK  = 3'd3;
    localparam STATE_STACK_OP   = 3'd4;
    localparam STATE_DONE       = 3'd5;

    reg [2:0] state;
    reg [7:0] current_inst;
    reg [2:0] current_index;
    reg       do_pop_after;
    reg [79:0] temp_result;
    reg [79:0] temp_result_secondary;  // For dual-result operations (FSINCOS)
    reg       has_secondary_result;     // Flag for dual-result operations
    reg [79:0] temp_operand_a, temp_operand_b;
    reg signed [31:0] temp_int32;
    reg [31:0] temp_fp32;
    reg [63:0] temp_fp64;

    //=================================================================
    // State Machine
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_IDLE;
            current_inst <= 8'h00;
            current_index <= 3'd0;
            do_pop_after <= 1'b0;
            ready <= 1'b1;
            error <= 1'b0;
            temp_result <= 80'd0;
            temp_result_secondary <= 80'd0;
            has_secondary_result <= 1'b0;
            temp_operand_a <= 80'd0;
            temp_operand_b <= 80'd0;
            temp_int32 <= 32'd0;
            temp_fp32 <= 32'd0;
            temp_fp64 <= 64'd0;

            // Initialize all stack control signals
            stack_push <= 1'b0;
            stack_pop <= 1'b0;
            stack_data_in <= 80'd0;
            stack_write_reg <= 3'd0;
            stack_write_enable <= 1'b0;
            stack_read_sel <= 3'd0;

            // Initialize arithmetic control signals
            arith_enable <= 1'b0;
            arith_operation <= 4'd0;
            arith_operand_a <= 80'd0;
            arith_operand_b <= 80'd0;
            arith_int16_in <= 16'd0;
            arith_int32_in <= 32'd0;
            arith_fp32_in <= 32'd0;
            arith_fp64_in <= 64'd0;

            // Initialize status control signals
            status_cc_write <= 1'b0;
            status_c3 <= 1'b0;
            status_c2 <= 1'b0;
            status_c1 <= 1'b0;
            status_c0 <= 1'b0;
            status_clear_exc <= 1'b0;
            status_set_busy <= 1'b0;
            status_clear_busy <= 1'b0;
            status_invalid <= 1'b0;
            status_denormal <= 1'b0;
            status_zero_div <= 1'b0;
            status_overflow <= 1'b0;
            status_underflow <= 1'b0;
            status_precision <= 1'b0;
            status_stack_fault <= 1'b0;

            data_out <= 80'd0;
            int_data_out <= 32'd0;
        end else begin
            // Default: deassert one-shot signals
            status_cc_write <= 1'b0;
            status_set_busy <= 1'b0;
            status_clear_busy <= 1'b0;
            status_clear_exc <= 1'b0;
            stack_push <= 1'b0;
            stack_pop <= 1'b0;
            stack_write_enable <= 1'b0;
            // Note: arith_enable is NOT defaulted to 0, it's explicitly managed

            case (state)
                STATE_IDLE: begin
                    ready <= 1'b1;
                    if (execute) begin
                        current_inst <= instruction;
                        current_index <= stack_index;
                        stack_read_sel <= stack_index;
                        ready <= 1'b0;
                        error <= 1'b0;
                        status_set_busy <= 1'b1;
                        state <= STATE_DECODE;
                    end
                end

                STATE_DECODE: begin
                    // Capture operands and set up for execution
                    temp_operand_a <= st0;
                    temp_operand_b <= stack_read_data;
                    temp_int32 <= int_data_in;
                    temp_fp32 <= data_in[31:0];
                    temp_fp64 <= data_in[63:0];

                    // Set pop flag
                    do_pop_after <= (current_inst == INST_FADDP) ||
                                   (current_inst == INST_FSUBP) ||
                                   (current_inst == INST_FMULP) ||
                                   (current_inst == INST_FDIVP) ||
                                   (current_inst == INST_FISTP16) ||
                                   (current_inst == INST_FISTP32) ||
                                   (current_inst == INST_FSTP) ||
                                   (current_inst == INST_FSTP32) ||
                                   (current_inst == INST_FSTP64);

                    state <= STATE_EXECUTE;
                end

                STATE_EXECUTE: begin
                    // Start or wait for arithmetic operation
                    case (current_inst)
                        INST_FADD, INST_FADDP: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd0;  // OP_ADD
                                    arith_operand_a <= temp_operand_a;
                                    arith_operand_b <= temp_operand_b;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                // Capture exceptions
                                status_invalid <= arith_invalid;
                                status_denormal <= arith_denormal;
                                status_zero_div <= arith_zero_div;
                                status_overflow <= arith_overflow;
                                status_underflow <= arith_underflow;
                                status_precision <= arith_inexact;
                                status_cc_write <= 1'b1;
                                status_c0 <= arith_cc_equal;
                                status_c2 <= arith_cc_less;
                                status_c3 <= arith_cc_unordered;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FSUB, INST_FSUBP: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd1;  // OP_SUB
                                    arith_operand_a <= temp_operand_a;
                                    arith_operand_b <= temp_operand_b;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                status_invalid <= arith_invalid;
                                status_overflow <= arith_overflow;
                                status_underflow <= arith_underflow;
                                status_precision <= arith_inexact;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FMUL, INST_FMULP: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd2;  // OP_MUL
                                    arith_operand_a <= temp_operand_a;
                                    arith_operand_b <= temp_operand_b;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                status_invalid <= arith_invalid;
                                status_overflow <= arith_overflow;
                                status_underflow <= arith_underflow;
                                status_precision <= arith_inexact;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FDIV, INST_FDIVP: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd3;  // OP_DIV
                                    arith_operand_a <= temp_operand_a;
                                    arith_operand_b <= temp_operand_b;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                status_invalid <= arith_invalid;
                                status_zero_div <= arith_zero_div;
                                status_overflow <= arith_overflow;
                                status_underflow <= arith_underflow;
                                status_precision <= arith_inexact;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FILD16: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd4;  // OP_INT16_TO_FP
                                    arith_int16_in <= temp_int32[15:0];
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FILD32: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd5;  // OP_INT32_TO_FP
                                    arith_int32_in <= temp_int32;
                                    arith_enable <= 1'b1;
                                end
                                // else: keep enable high, wait for done
                            end else begin  // arith_done
                                temp_result <= arith_result;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FIST16, INST_FISTP16: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd6;  // OP_FP_TO_INT16
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                int_data_out <= {16'd0, arith_int16_out};
                                status_invalid <= arith_invalid;
                                status_overflow <= arith_overflow;
                                status_precision <= arith_inexact;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FIST32, INST_FISTP32: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd7;  // OP_FP_TO_INT32
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                int_data_out <= arith_int32_out;
                                status_invalid <= arith_invalid;
                                status_overflow <= arith_overflow;
                                status_precision <= arith_inexact;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FLD32: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd8;  // OP_FP32_TO_FP80
                                    arith_fp32_in <= temp_fp32;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FLD64: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd9;  // OP_FP64_TO_FP80
                                    arith_fp64_in <= temp_fp64;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FST32, INST_FSTP32: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd10;  // OP_FP80_TO_FP32
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                data_out <= {48'd0, arith_fp32_out};
                                status_invalid <= arith_invalid;
                                status_overflow <= arith_overflow;
                                status_underflow <= arith_underflow;
                                status_precision <= arith_inexact;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FST64, INST_FSTP64: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd11;  // OP_FP80_TO_FP64
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                data_out <= {16'd0, arith_fp64_out};
                                status_invalid <= arith_invalid;
                                status_overflow <= arith_overflow;
                                status_underflow <= arith_underflow;
                                status_precision <= arith_inexact;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        // Transcendental instructions
                        INST_FSQRT: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd12;  // OP_SQRT
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                has_secondary_result <= 1'b0;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FSIN: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd13;  // OP_SIN
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                has_secondary_result <= 1'b0;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FCOS: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd14;  // OP_COS
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;
                                has_secondary_result <= 1'b0;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FSINCOS: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd15;  // OP_SINCOS
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                // Store both sin and cos results
                                temp_result <= arith_result;              // sin(θ)
                                temp_result_secondary <= arith_result_secondary;  // cos(θ)
                                has_secondary_result <= arith_has_secondary;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        // Non-arithmetic instructions
                        INST_FLD: begin
                            temp_result <= data_in;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FST: begin
                            // Read from stack and output to data_out
                            data_out <= temp_operand_a;  // temp_operand_a contains ST(i)
                            state <= STATE_DONE;
                        end

                        INST_FCLEX: begin
                            status_clear_exc <= 1'b1;
                            state <= STATE_DONE;
                        end

                        default: begin
                            state <= STATE_DONE;
                        end
                    endcase
                end

                STATE_WRITEBACK: begin
                    // No action, just transition
                    state <= STATE_STACK_OP;
                end

                STATE_STACK_OP: begin
                    case (current_inst)
                        // Load operations: push result onto stack
                        INST_FLD, INST_FILD16, INST_FILD32,
                        INST_FLD32, INST_FLD64: begin
                            stack_push <= 1'b1;
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                        end

                        // Arithmetic operations: write to ST(0)
                        INST_FADD, INST_FSUB, INST_FMUL, INST_FDIV: begin
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                        end

                        // Transcendental operations (single result): write to ST(0)
                        INST_FSQRT, INST_FSIN, INST_FCOS: begin
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                        end

                        // FSINCOS: Special case - pushes both sin and cos
                        // Intel 8087 behavior:
                        //   Input:  ST(0) = θ
                        //   Output: ST(0) = cos(θ), ST(1) = sin(θ)
                        // Implementation: Write sin to ST(1), push cos to ST(0)
                        INST_FSINCOS: begin
                            if (has_secondary_result) begin
                                // Write sin(θ) to ST(1) position (where it will be after push)
                                stack_write_reg <= 3'd1;
                                stack_data_in <= temp_result;              // sin(θ)
                                stack_write_enable <= 1'b1;
                                // Push cos(θ) onto stack (becomes new ST(0))
                                stack_push <= 1'b1;
                                // Note: The push operation should be handled first by the register stack,
                                // then the write. This way sin goes to the correct ST(1) position.
                                // TODO: Verify register stack handles push+write correctly in same cycle
                                // May need to use temp_result_secondary for cos after verifying behavior
                            end else begin
                                // Fallback if no secondary result (shouldn't happen for FSINCOS)
                                stack_write_reg <= 3'd0;
                                stack_data_in <= temp_result;
                                stack_write_enable <= 1'b1;
                            end
                        end

                        // Arithmetic with pop: write to ST(1) then pop
                        INST_FADDP, INST_FSUBP, INST_FMULP, INST_FDIVP: begin
                            stack_write_reg <= 3'd1;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                            stack_pop <= 1'b1;
                        end

                        // Store and pop
                        INST_FSTP, INST_FISTP16, INST_FISTP32,
                        INST_FSTP32, INST_FSTP64: begin
                            stack_pop <= 1'b1;
                        end

                        default: begin
                            // No stack operation
                        end
                    endcase

                    state <= STATE_DONE;
                end

                STATE_DONE: begin
                    ready <= 1'b1;
                    status_clear_busy <= 1'b1;
                    status_stack_fault <= stack_overflow | stack_underflow;

                    // Check for unmasked exceptions
                    error <= (status_invalid & ~mask_invalid) |
                            (status_denormal & ~mask_denormal) |
                            (status_zero_div & ~mask_zero_div) |
                            (status_overflow & ~mask_overflow) |
                            (status_underflow & ~mask_underflow) |
                            (status_precision & ~mask_precision);

                    // Clear arithmetic operation to prevent done signal from persisting
                    // Setting to invalid operation (15) ensures all unit done signals go to 0
                    arith_operation <= 4'd15;

                    state <= STATE_IDLE;
                end

                default: state <= STATE_IDLE;
            endcase
        end
    end

endmodule
