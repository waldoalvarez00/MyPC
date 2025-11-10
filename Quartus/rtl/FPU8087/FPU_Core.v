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

    // Memory operand format information (from decoder)
    input wire        has_memory_op,    // Instruction uses memory operand
    input wire [1:0]  operand_size,     // Memory operand size (0=word, 1=dword, 2=qword, 3=tbyte)
    input wire        is_integer,       // Memory operand is integer format
    input wire        is_bcd,           // Memory operand is BCD format

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

    // BCD conversion
    localparam INST_FBLD        = 8'h36;  // Load BCD (18 digits)
    localparam INST_FBSTP       = 8'h37;  // Store BCD and pop

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

    // Comparison instructions
    localparam INST_FCOM        = 8'h60;  // Compare ST(0) with ST(i) or memory
    localparam INST_FCOMP       = 8'h61;  // Compare and pop
    localparam INST_FCOMPP      = 8'h62;  // Compare ST(0) with ST(1) and pop twice
    localparam INST_FTST        = 8'h63;  // Test ST(0) against 0.0
    localparam INST_FXAM        = 8'h64;  // Examine ST(0) and set condition codes

    // Reverse arithmetic (decoder provides these)
    localparam INST_FSUBR       = 8'h14;  // ST(0) = ST(i) - ST(0) (reverse subtract)
    localparam INST_FSUBRP      = 8'h15;  // ST(1) = ST(1) - ST(0), pop
    localparam INST_FDIVR       = 8'h1A;  // ST(0) = ST(i) / ST(0) (reverse divide)
    localparam INST_FDIVRP      = 8'h1B;  // ST(1) = ST(1) / ST(0), pop

    // Unordered compare
    localparam INST_FUCOM       = 8'h65;  // Unordered compare ST(0) with ST(i)
    localparam INST_FUCOMP      = 8'h66;  // Unordered compare and pop
    localparam INST_FUCOMPP     = 8'h67;  // Unordered compare ST(0) with ST(1) and pop twice

    // Stack management instructions
    localparam INST_FINCSTP     = 8'h70;  // Increment stack pointer
    localparam INST_FDECSTP     = 8'h71;  // Decrement stack pointer
    localparam INST_FFREE       = 8'h72;  // Mark register as empty
    localparam INST_FNOP        = 8'h73;  // No operation

    // Constants
    localparam INST_FLD1        = 8'h80;  // Push +1.0
    localparam INST_FLDZ        = 8'h81;  // Push +0.0
    localparam INST_FLDPI       = 8'h82;  // Push π
    localparam INST_FLDL2E      = 8'h83;  // Push log₂(e)
    localparam INST_FLDL2T      = 8'h84;  // Push log₂(10)
    localparam INST_FLDLG2      = 8'h85;  // Push log₁₀(2)
    localparam INST_FLDLN2      = 8'h86;  // Push ln(2)

    // Advanced operations
    localparam INST_FSCALE      = 8'h90;  // Scale ST(0) by power of 2 from ST(1)
    localparam INST_FXTRACT     = 8'h91;  // Extract exponent and significand
    localparam INST_FPREM       = 8'h92;  // Partial remainder
    localparam INST_FRNDINT     = 8'h93;  // Round to integer
    localparam INST_FABS        = 8'h94;  // Absolute value: ST(0) = |ST(0)|
    localparam INST_FCHS        = 8'h95;  // Change sign: ST(0) = -ST(0)

    // Control instructions
    localparam INST_FINIT       = 8'hF0;  // Initialize FPU
    localparam INST_FLDCW       = 8'hF1;  // Load control word
    localparam INST_FSTCW       = 8'hF2;  // Store control word
    localparam INST_FSTSW       = 8'hF3;  // Store status word
    localparam INST_FCLEX       = 8'hF4;  // Clear exceptions
    localparam INST_FWAIT       = 8'hF5;  // Wait for FPU ready

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
    reg         stack_inc_ptr;     // Increment stack pointer (FINCSTP)
    reg         stack_dec_ptr;     // Decrement stack pointer (FDECSTP)
    reg         stack_free_reg;    // Mark register as free (FFREE)
    reg [2:0]   stack_free_index;  // Index of register to free

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
        .stack_underflow(stack_underflow),
        .inc_ptr(stack_inc_ptr),
        .dec_ptr(stack_dec_ptr),
        .free_reg(stack_free_reg),
        .free_index(stack_free_index)
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
    wire [63:0] arith_uint64_out;      // Unsigned 64-bit for BCD
    wire        arith_uint64_sign_out; // Sign bit for uint64
    wire [31:0] arith_fp32_out;
    wire [63:0] arith_fp64_out;
    wire        arith_done;
    wire        arith_cc_less, arith_cc_equal, arith_cc_greater, arith_cc_unordered;
    wire        arith_invalid, arith_denormal, arith_zero_div;
    wire        arith_overflow, arith_underflow, arith_inexact;

    reg [4:0]   arith_operation;  // 5 bits to support operations 0-17 (BCD uses 16-17)
    reg         arith_enable;
    reg [79:0]  arith_operand_a, arith_operand_b;
    reg signed [15:0] arith_int16_in;
    reg signed [31:0] arith_int32_in;
    reg [63:0]  arith_uint64_in;       // Unsigned 64-bit for BCD
    reg         arith_uint64_sign_in;  // Sign bit for uint64
    reg [31:0]  arith_fp32_in;
    reg [63:0]  arith_fp64_in;

    FPU_ArithmeticUnit arithmetic_unit (
        .clk(clk),
        .reset(reset),
        .operation(final_arith_operation),
        .enable(final_arith_enable),
        .rounding_mode(rounding_mode),
        .operand_a(final_arith_operand_a),
        .operand_b(final_arith_operand_b),
        .int16_in(final_arith_int16_in),
        .int32_in(final_arith_int32_in),
        .uint64_in(final_arith_uint64_in),
        .uint64_sign_in(final_arith_uint64_sign_in),
        .fp32_in(final_arith_fp32_in),
        .fp64_in(final_arith_fp64_in),
        .result(arith_result),
        .result_secondary(arith_result_secondary),
        .has_secondary(arith_has_secondary),
        .int16_out(arith_int16_out),
        .int32_out(arith_int32_out),
        .uint64_out(arith_uint64_out),
        .uint64_sign_out(arith_uint64_sign_out),
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
    // BCD Converters
    //=================================================================

    // BCD to Binary
    wire [63:0] bcd2bin_binary_out;
    wire        bcd2bin_sign_out;
    wire        bcd2bin_done;
    wire        bcd2bin_error;

    reg         bcd2bin_enable;
    reg [79:0]  bcd2bin_bcd_in;

    FPU_BCD_to_Binary bcd_to_binary (
        .clk(clk),
        .reset(reset),
        .enable(final_bcd2bin_enable),
        .bcd_in(final_bcd2bin_bcd_in),
        .binary_out(bcd2bin_binary_out),
        .sign_out(bcd2bin_sign_out),
        .done(bcd2bin_done),
        .error(bcd2bin_error)
    );

    // Binary to BCD
    wire [79:0] bin2bcd_bcd_out;
    wire        bin2bcd_done;
    wire        bin2bcd_error;

    reg         bin2bcd_enable;
    reg [63:0]  bin2bcd_binary_in;
    reg         bin2bcd_sign_in;

    FPU_Binary_to_BCD binary_to_bcd (
        .clk(clk),
        .reset(reset),
        .enable(final_bin2bcd_enable),
        .binary_in(final_bin2bcd_binary_in),
        .sign_in(final_bin2bcd_sign_in),
        .bcd_out(bin2bcd_bcd_out),
        .done(bin2bcd_done),
        .error(bin2bcd_error)
    );

    //=================================================================
    // BCD Microsequencer
    //=================================================================

    // Microsequencer control signals
    reg        microseq_start;
    reg [3:0]  microseq_program_index;
    wire       microseq_complete;
    wire [79:0] microseq_data_out;
    wire [79:0] microseq_temp_result;  // Debug output: temp_result from microsequencer
    reg [79:0]  microseq_data_in_source;  // Multiplexed data input (external data_in or temp_operand_a)

    // Microsequencer interfaces to hardware units (connect to same units as FPU_Core)
    wire [4:0]  microseq_arith_operation;
    wire        microseq_arith_enable;
    // Note: rounding_mode comes directly from control word, not from microsequencer
    wire [79:0] microseq_arith_operand_a;
    wire [79:0] microseq_arith_operand_b;
    wire signed [15:0] microseq_arith_int16_in;
    wire signed [31:0] microseq_arith_int32_in;
    wire [63:0] microseq_arith_uint64_in;
    wire        microseq_arith_uint64_sign_in;
    wire [31:0] microseq_arith_fp32_in;
    wire [63:0] microseq_arith_fp64_in;

    wire        microseq_bcd2bin_enable;
    wire [79:0] microseq_bcd2bin_bcd_in;

    wire        microseq_bin2bcd_enable;
    wire [63:0] microseq_bin2bcd_binary_in;
    wire        microseq_bin2bcd_sign_in;

    // Shared control: when microsequencer is active, it controls the hardware units
    reg microseq_active;

    // Multiplex hardware unit control between FPU_Core FSM and microsequencer
    // Note: rounding_mode always comes from control word, not multiplexed
    wire        final_arith_enable = microseq_active ? microseq_arith_enable : arith_enable;
    wire [4:0]  final_arith_operation = microseq_active ? microseq_arith_operation : arith_operation;
    wire [79:0] final_arith_operand_a = microseq_active ? microseq_arith_operand_a : arith_operand_a;
    wire [79:0] final_arith_operand_b = microseq_active ? microseq_arith_operand_b : arith_operand_b;
    wire signed [15:0] final_arith_int16_in = microseq_active ? microseq_arith_int16_in : arith_int16_in;
    wire signed [31:0] final_arith_int32_in = microseq_active ? microseq_arith_int32_in : arith_int32_in;
    wire [63:0] final_arith_uint64_in = microseq_active ? microseq_arith_uint64_in : arith_uint64_in;
    wire        final_arith_uint64_sign_in = microseq_active ? microseq_arith_uint64_sign_in : arith_uint64_sign_in;
    wire [31:0] final_arith_fp32_in = microseq_active ? microseq_arith_fp32_in : arith_fp32_in;
    wire [63:0] final_arith_fp64_in = microseq_active ? microseq_arith_fp64_in : arith_fp64_in;

    wire        final_bcd2bin_enable = microseq_active ? microseq_bcd2bin_enable : bcd2bin_enable;
    wire [79:0] final_bcd2bin_bcd_in = microseq_active ? microseq_bcd2bin_bcd_in : bcd2bin_bcd_in;

    wire        final_bin2bcd_enable = microseq_active ? microseq_bin2bcd_enable : bin2bcd_enable;
    wire [63:0] final_bin2bcd_binary_in = microseq_active ? microseq_bin2bcd_binary_in : bin2bcd_binary_in;
    wire        final_bin2bcd_sign_in = microseq_active ? microseq_bin2bcd_sign_in : bin2bcd_sign_in;

    MicroSequencer_Extended_BCD microsequencer (
        .clk(clk),
        .reset(reset),

        // Control interface
        .start(microseq_start),
        .micro_program_index(microseq_program_index),
        .instruction_complete(microseq_complete),

        // Data bus interface
        .data_in(microseq_data_in_source),  // Multiplexed: data_in for FBLD, temp_operand_a for FBSTP
        .data_out(microseq_data_out),

        // Debug interface (used for FBLD result)
        .debug_temp_result(microseq_temp_result),
        .debug_temp_fp_a(),
        .debug_temp_fp_b(),
        .debug_temp_uint64(),
        .debug_temp_sign(),

        // Interface to FPU_ArithmeticUnit
        .arith_operation(microseq_arith_operation),
        .arith_enable(microseq_arith_enable),
        .arith_rounding_mode(rounding_mode),  // Use control word rounding mode
        .arith_operand_a(microseq_arith_operand_a),
        .arith_operand_b(microseq_arith_operand_b),
        .arith_int16_in(microseq_arith_int16_in),
        .arith_int32_in(microseq_arith_int32_in),
        .arith_uint64_in(microseq_arith_uint64_in),
        .arith_uint64_sign_in(microseq_arith_uint64_sign_in),
        .arith_fp32_in(microseq_arith_fp32_in),
        .arith_fp64_in(microseq_arith_fp64_in),
        .arith_result(arith_result),
        .arith_int16_out(arith_int16_out),
        .arith_int32_out(arith_int32_out),
        .arith_uint64_out(arith_uint64_out),
        .arith_uint64_sign_out(arith_uint64_sign_out),
        .arith_fp32_out(arith_fp32_out),
        .arith_fp64_out(arith_fp64_out),
        .arith_done(arith_done),
        .arith_invalid(arith_invalid),
        .arith_overflow(arith_overflow),
        .arith_cc_less(arith_cc_less),
        .arith_cc_equal(arith_cc_equal),
        .arith_cc_greater(arith_cc_greater),
        .arith_cc_unordered(arith_cc_unordered),

        // Interface to BCD converters
        .bcd2bin_enable(microseq_bcd2bin_enable),
        .bcd2bin_bcd_in(microseq_bcd2bin_bcd_in),
        .bcd2bin_binary_out(bcd2bin_binary_out),
        .bcd2bin_sign_out(bcd2bin_sign_out),
        .bcd2bin_done(bcd2bin_done),
        .bcd2bin_error(bcd2bin_error),

        .bin2bcd_enable(microseq_bin2bcd_enable),
        .bin2bcd_binary_in(microseq_bin2bcd_binary_in),
        .bin2bcd_sign_in(microseq_bin2bcd_sign_in),
        .bin2bcd_bcd_out(bin2bcd_bcd_out),
        .bin2bcd_done(bin2bcd_done),
        .bin2bcd_error(bin2bcd_error),

        // Stack interface (unused for BCD programs)
        .stack_push_req(),
        .stack_pop_req(),
        .stack_read_sel(),
        .stack_write_sel(),
        .stack_write_en(),
        .stack_write_data(),
        .stack_read_data(80'd0),
        .stack_op_done(1'b0),

        // Status/control interface (unused for BCD programs)
        .status_word_in(16'd0),
        .status_word_out(),
        .status_word_write(),
        .control_word_in(16'd0),
        .control_word_out(),
        .control_word_write()
    );

    //=================================================================
    // Execution State Machine
    //=================================================================

    localparam STATE_IDLE          = 4'd0;
    localparam STATE_DECODE        = 4'd1;
    localparam STATE_EXECUTE       = 4'd2;
    localparam STATE_WRITEBACK     = 4'd3;
    localparam STATE_STACK_OP      = 4'd4;
    localparam STATE_DONE          = 4'd5;
    localparam STATE_FSINCOS_PUSH  = 4'd6;  // Second cycle of FSINCOS writeback
    localparam STATE_FXCH_WRITE2   = 4'd7;  // Second cycle of FXCH writeback
    localparam STATE_FCOMPP_POP2   = 4'd8;  // Second cycle of FCOMPP (second pop)
    localparam STATE_MEM_CONVERT   = 4'd9;  // Memory operand format conversion
    localparam STATE_WAIT_MICROSEQ = 4'd10; // Wait for microsequencer to complete BCD operation

    reg [3:0] state;
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

    // Captured memory operand format flags (from inputs, captured in STATE_DECODE)
    reg       captured_has_memory_op;
    reg [1:0] captured_operand_size;
    reg       captured_is_integer;
    reg       captured_is_bcd;

    // Memory conversion tracking
    reg       mem_conv_active;         // Memory conversion in progress
    reg       mem_conv_stage2;         // Second stage of two-stage conversion (BCD)
    reg [1:0] mem_conv_size;           // Size of memory operand being converted
    reg       mem_conv_is_load;        // True for load (FLD), false for store (FST)
    reg [63:0] temp_uint64;            // Temporary storage for BCD two-stage conversion

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

            // Initialize captured memory format flags
            captured_has_memory_op <= 1'b0;
            captured_operand_size <= 2'd0;
            captured_is_integer <= 1'b0;
            captured_is_bcd <= 1'b0;

            // Initialize memory conversion tracking
            mem_conv_active <= 1'b0;
            mem_conv_stage2 <= 1'b0;
            mem_conv_size <= 2'd0;
            mem_conv_is_load <= 1'b0;
            temp_uint64 <= 64'd0;

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
            arith_uint64_in <= 64'd0;
            arith_uint64_sign_in <= 1'b0;
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

            // Initialize BCD converter signals
            bcd2bin_enable <= 1'b0;
            bcd2bin_bcd_in <= 80'd0;
            bin2bcd_enable <= 1'b0;
            bin2bcd_binary_in <= 64'd0;
            bin2bcd_sign_in <= 1'b0;

            // Initialize microsequencer signals
            microseq_start <= 1'b0;
            microseq_program_index <= 4'd0;
            microseq_active <= 1'b0;
            microseq_data_in_source <= 80'd0;

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
            stack_inc_ptr <= 1'b0;
            stack_dec_ptr <= 1'b0;
            stack_free_reg <= 1'b0;
            microseq_start <= 1'b0;  // One-shot signal for microsequencer
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

                        // Capture memory operation format flags immediately
                        // (they may be cleared by testbench before STATE_DECODE/EXECUTE)
                        captured_has_memory_op <= has_memory_op;
                        captured_operand_size <= operand_size;
                        captured_is_integer <= is_integer;
                        captured_is_bcd <= is_bcd;

                        state <= STATE_DECODE;
                    end
                end

                STATE_DECODE: begin
                    // Capture operands and set up for execution
                    temp_operand_a <= st0;
                    temp_operand_b <= stack_read_data;

                    // Handle memory operand format based on decoder flags (already captured in STATE_IDLE)
                    if (has_memory_op) begin
                        // Memory operand - capture based on size and type
                        case (operand_size)
                            2'd0: temp_int32 <= {{16{data_in[15]}}, data_in[15:0]};  // Sign-extend 16-bit
                            2'd1: temp_int32 <= data_in[31:0];                         // 32-bit
                            2'd2: begin                                                 // 64-bit
                                temp_fp64 <= data_in[63:0];
                            end
                            2'd3: begin                                                 // 80-bit
                                // 80-bit operand - already in correct format
                            end
                        endcase

                        // Store FP32/FP64 separately
                        temp_fp32 <= data_in[31:0];
                        temp_fp64 <= data_in[63:0];
                    end else begin
                        // Register operand - use default
                        temp_int32 <= int_data_in;
                        temp_fp32 <= data_in[31:0];
                        temp_fp64 <= data_in[63:0];
                    end

                    // Set pop flag
                    do_pop_after <= (current_inst == INST_FADDP) ||
                                   (current_inst == INST_FSUBP) ||
                                   (current_inst == INST_FMULP) ||
                                   (current_inst == INST_FDIVP) ||
                                   (current_inst == INST_FSUBRP) ||
                                   (current_inst == INST_FDIVRP) ||
                                   (current_inst == INST_FISTP16) ||
                                   (current_inst == INST_FISTP32) ||
                                   (current_inst == INST_FBSTP) ||
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

                        INST_FST, INST_FSTP: begin
                            // Store FP80 (no conversion needed)
                            data_out <= temp_operand_a;  // ST(0) → data_out
                            state <= STATE_STACK_OP;
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

                        INST_FPTAN: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 5'd18;  // OP_TAN
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                // Store tan and 1.0 (for compatibility with 8087)
                                temp_result <= arith_result;              // tan(θ)
                                temp_result_secondary <= arith_result_secondary;  // 1.0
                                has_secondary_result <= arith_has_secondary;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FPATAN: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 5'd19;  // OP_ATAN
                                    arith_operand_a <= temp_operand_a;  // y (ST(1))
                                    arith_operand_b <= temp_operand_b;  // x (ST(0))
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;  // atan(y/x)
                                has_secondary_result <= 1'b0;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_F2XM1: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 5'd20;  // OP_F2XM1
                                    arith_operand_a <= temp_operand_a;
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;  // 2^x - 1
                                has_secondary_result <= 1'b0;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FYL2X: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 5'd21;  // OP_FYL2X
                                    arith_operand_a <= temp_operand_b;  // x (ST(0))
                                    arith_operand_b <= temp_operand_a;  // y (ST(1))
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;  // y × log₂(x)
                                has_secondary_result <= 1'b0;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FYL2XP1: begin
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 5'd22;  // OP_FYL2XP1
                                    arith_operand_a <= temp_operand_b;  // x (ST(0))
                                    arith_operand_b <= temp_operand_a;  // y (ST(1))
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                temp_result <= arith_result;  // y × log₂(x+1)
                                has_secondary_result <= 1'b0;
                                status_invalid <= arith_invalid;
                                arith_enable <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        // BCD conversion instructions
                        INST_FBLD: begin
                            // BCD Load: Use microcode program 12 (BCD → Binary → FP80)
                            // This replaces ~33 lines of FSM orchestration logic with a single microcode call
                            microseq_data_in_source <= data_in;  // BCD input from memory/CPU
                            microseq_program_index <= 4'd12;  // Program 12: FBLD at 0x0600
                            microseq_start <= 1'b1;
                            microseq_active <= 1'b1;
                            state <= STATE_WAIT_MICROSEQ;
                        end

                        INST_FBSTP: begin
                            // BCD Store and Pop: Use microcode program 13 (FP80 → Binary → BCD)
                            // This replaces ~37 lines of FSM orchestration logic with a single microcode call
                            microseq_data_in_source <= temp_operand_a;  // FP80 value from ST(0)
                            microseq_program_index <= 4'd13;  // Program 13: FBSTP at 0x0610
                            microseq_start <= 1'b1;
                            microseq_active <= 1'b1;
                            state <= STATE_WAIT_MICROSEQ;
                        end

                        // Non-arithmetic instructions
                        INST_FLD: begin
                            if (captured_has_memory_op && (captured_operand_size != 2'd3 || captured_is_bcd)) begin
                                // Memory operand that needs format conversion
                                // Set up conversion and transition to STATE_MEM_CONVERT
                                $display("[DEBUG] INST_FLD: Memory op, needs conversion. operand_size=%d, is_integer=%b, is_bcd=%b",
                                        captured_operand_size, captured_is_integer, captured_is_bcd);
                                mem_conv_active <= 1'b1;
                                mem_conv_stage2 <= 1'b0;
                                mem_conv_size <= captured_operand_size;
                                mem_conv_is_load <= 1'b1;
                                state <= STATE_MEM_CONVERT;
                            end else begin
                                // No conversion needed (FP80 or register operand)
                                $display("[DEBUG] INST_FLD: No conversion needed. has_memory_op=%b, operand_size=%d",
                                        captured_has_memory_op, captured_operand_size);
                                temp_result <= data_in;
                                state <= STATE_WRITEBACK;
                            end
                        end

                        INST_FST: begin
                            if (captured_has_memory_op && (captured_operand_size != 2'd3 || captured_is_bcd)) begin
                                // Memory operand that needs format conversion
                                // Set up conversion and transition to STATE_MEM_CONVERT
                                mem_conv_active <= 1'b1;
                                mem_conv_stage2 <= 1'b0;
                                mem_conv_size <= captured_operand_size;
                                mem_conv_is_load <= 1'b0;  // Store operation
                                state <= STATE_MEM_CONVERT;
                            end else begin
                                // No conversion needed (FP80 or register operand)
                                data_out <= (current_index == 0) ? temp_operand_a : temp_operand_b;
                                state <= STATE_DONE;
                            end
                        end

                        INST_FXCH: begin
                            // Exchange ST(0) with ST(i)
                            // temp_operand_a = ST(0), temp_operand_b = ST(i)
                            // Swap them for writeback
                            temp_result <= temp_operand_b;            // ST(i) → will write to ST(0)
                            temp_result_secondary <= temp_operand_a;  // ST(0) → will write to ST(i)
                            has_secondary_result <= 1'b1;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FCLEX: begin
                            status_clear_exc <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Stack management instructions
                        INST_FINCSTP: begin
                            // Increment stack pointer (no data transfer)
                            stack_inc_ptr <= 1'b1;
                            state <= STATE_DONE;
                        end

                        INST_FDECSTP: begin
                            // Decrement stack pointer (no data transfer)
                            stack_dec_ptr <= 1'b1;
                            state <= STATE_DONE;
                        end

                        INST_FFREE: begin
                            // Mark register ST(i) as empty
                            stack_free_reg <= 1'b1;
                            stack_free_index <= current_index;
                            state <= STATE_DONE;
                        end

                        // Comparison instructions
                        INST_FCOM, INST_FCOMP: begin
                            // Compare ST(0) with ST(i) or memory operand
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    // Use ADD operation for comparison (SUB would flip sign of operand_b!)
                                    arith_operation <= 5'd0;  // OP_ADD (comparison uses same logic, no sign flip)
                                    arith_operand_a <= temp_operand_a;  // ST(0)
                                    arith_operand_b <= temp_operand_b;  // ST(i) or memory
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                // Map comparison results to condition codes per Intel 8087 spec
                                // C3 C2 C0:
                                //   000 = ST(0) > operand
                                //   001 = ST(0) < operand
                                //   100 = ST(0) = operand
                                //   111 = Unordered (NaN)
                                status_cc_write <= 1'b1;
                                if (arith_cc_unordered) begin
                                    status_c3 <= 1'b1;
                                    status_c2 <= 1'b1;
                                    status_c0 <= 1'b1;
                                end else begin
                                    status_c3 <= arith_cc_equal;
                                    status_c2 <= 1'b0;
                                    status_c0 <= arith_cc_less;
                                end
                                arith_enable <= 1'b0;
                                state <= STATE_STACK_OP;
                            end
                        end

                        INST_FCOMPP: begin
                            // Compare ST(0) with ST(1) and pop twice
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    // Use ADD for comparison (no sign flip)
                                    arith_operation <= 5'd0;  // OP_ADD
                                    arith_operand_a <= temp_operand_a;  // ST(0)
                                    arith_operand_b <= temp_operand_b;  // ST(1)
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                // Set condition codes
                                status_cc_write <= 1'b1;
                                if (arith_cc_unordered) begin
                                    status_c3 <= 1'b1;
                                    status_c2 <= 1'b1;
                                    status_c0 <= 1'b1;
                                end else begin
                                    status_c3 <= arith_cc_equal;
                                    status_c2 <= 1'b0;
                                    status_c0 <= arith_cc_less;
                                end
                                arith_enable <= 1'b0;
                                state <= STATE_STACK_OP;
                            end
                        end

                        INST_FTST: begin
                            // Test ST(0) against +0.0
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    // Use ADD for comparison (no sign flip)
                                    arith_operation <= 5'd0;  // OP_ADD
                                    arith_operand_a <= temp_operand_a;  // ST(0)
                                    arith_operand_b <= 80'h0000_0000000000000000;  // +0.0
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                // Set condition codes
                                status_cc_write <= 1'b1;
                                if (arith_cc_unordered) begin
                                    status_c3 <= 1'b1;
                                    status_c2 <= 1'b1;
                                    status_c0 <= 1'b1;
                                end else begin
                                    status_c3 <= arith_cc_equal;
                                    status_c2 <= 1'b0;
                                    status_c0 <= arith_cc_less;
                                end
                                arith_enable <= 1'b0;
                                state <= STATE_DONE;
                            end
                        end

                        INST_FXAM: begin
                            // Examine ST(0) and classify
                            // Set condition codes C0, C2, C3 based on classification
                            // Intel 8087 FXAM encoding (C3 C2 C0):
                            //   000 = +Unnormal      001 = +NaN
                            //   010 = -Unnormal      011 = -NaN
                            //   100 = +Normal        101 = +Infinity
                            //   110 = -Normal        111 = -Infinity
                            // Special cases for zero and denormal

                            status_cc_write <= 1'b1;

                            // Classify based on exponent and mantissa fields
                            if (temp_operand_a[78:64] == 15'd0) begin
                                // Exponent is zero
                                if (temp_operand_a[63:0] == 64'd0) begin
                                    // Zero: C3=1, C2=0, C0=sign
                                    status_c3 <= 1'b1;
                                    status_c2 <= 1'b0;
                                    status_c0 <= temp_operand_a[79];
                                end else begin
                                    // Denormal: C3=1, C2=1, C0=sign
                                    status_c3 <= 1'b1;
                                    status_c2 <= 1'b1;
                                    status_c0 <= temp_operand_a[79];
                                end
                            end else if (temp_operand_a[78:64] == 15'h7FFF) begin
                                // Exponent is all ones (infinity or NaN)
                                if (temp_operand_a[63] == 1'b0 || temp_operand_a[62:0] != 63'd0) begin
                                    // NaN: C3=0, C2=0, C0=1
                                    status_c3 <= 1'b0;
                                    status_c2 <= 1'b0;
                                    status_c0 <= 1'b1;
                                end else begin
                                    // Infinity: C3=0, C2=1, C0=1
                                    status_c3 <= 1'b0;
                                    status_c2 <= 1'b1;
                                    status_c0 <= 1'b1;
                                end
                            end else begin
                                // Normal number: C3=0, C2=1, C0=0
                                status_c3 <= 1'b0;
                                status_c2 <= 1'b1;
                                status_c0 <= 1'b0;
                            end

                            // C1 contains sign bit
                            status_c1 <= temp_operand_a[79];

                            state <= STATE_DONE;
                        end

                        // ===== Trivial Operations =====

                        INST_FABS: begin
                            // Absolute value: Clear sign bit of ST(0)
                            temp_result <= {1'b0, temp_operand_a[78:0]};
                            state <= STATE_WRITEBACK;
                        end

                        INST_FCHS: begin
                            // Change sign: Flip sign bit of ST(0)
                            temp_result <= {~temp_operand_a[79], temp_operand_a[78:0]};
                            state <= STATE_WRITEBACK;
                        end

                        INST_FNOP: begin
                            // No operation
                            state <= STATE_DONE;
                        end

                        INST_FWAIT: begin
                            // Wait for FPU ready (no-op in single-threaded implementation)
                            state <= STATE_DONE;
                        end

                        // ===== Constant Loading Instructions =====

                        INST_FLD1: begin
                            // Push +1.0: sign=0, exp=16383 (0x3FFF), mantissa=0x8000000000000000
                            temp_result <= 80'h3FFF8000000000000000;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FLDZ: begin
                            // Push +0.0: All zeros
                            temp_result <= 80'h00000000000000000000;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FLDPI: begin
                            // Push π ≈ 3.141592653589793238
                            // FP80: sign=0, exp=16384 (0x4000), mantissa=0xC90FDAA22168C235
                            temp_result <= 80'h4000C90FDAA22168C235;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FLDL2E: begin
                            // Push log₂(e) ≈ 1.442695040888963407
                            // FP80: sign=0, exp=16383 (0x3FFF), mantissa=0xB8AA3B295C17F0BC
                            temp_result <= 80'h3FFFB8AA3B295C17F0BC;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FLDL2T: begin
                            // Push log₂(10) ≈ 3.321928094887362347
                            // FP80: sign=0, exp=16384 (0x4000), mantissa=0xD49A784BCD1B8AFE
                            temp_result <= 80'h4000D49A784BCD1B8AFE;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FLDLG2: begin
                            // Push log₁₀(2) ≈ 0.301029995663981195
                            // FP80: sign=0, exp=16382 (0x3FFD), mantissa=0x9A209A84FBCFF799
                            temp_result <= 80'h3FFD9A209A84FBCFF799;
                            state <= STATE_WRITEBACK;
                        end

                        INST_FLDLN2: begin
                            // Push ln(2) ≈ 0.693147180559945309
                            // FP80: sign=0, exp=16382 (0x3FFE), mantissa=0xB17217F7D1CF79AC
                            temp_result <= 80'h3FFEB17217F7D1CF79AC;
                            state <= STATE_WRITEBACK;
                        end

                        // ===== Reverse Arithmetic Operations =====

                        INST_FSUBR, INST_FSUBRP: begin
                            // Reverse subtract: ST(0) = ST(i) - ST(0)
                            // Swap operands compared to FSUB
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd1;  // OP_SUB
                                    arith_operand_a <= temp_operand_b;  // Swapped!
                                    arith_operand_b <= temp_operand_a;  // Swapped!
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

                        INST_FDIVR, INST_FDIVRP: begin
                            // Reverse divide: ST(0) = ST(i) / ST(0)
                            // Swap operands compared to FDIV
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 4'd3;  // OP_DIV
                                    arith_operand_a <= temp_operand_b;  // Swapped!
                                    arith_operand_b <= temp_operand_a;  // Swapped!
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

                        // ===== Unordered Compare Operations =====

                        INST_FUCOM, INST_FUCOMP: begin
                            // Unordered compare - like FCOM but doesn't raise exception on NaN
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 5'd0;  // OP_ADD (for comparison)
                                    arith_operand_a <= temp_operand_a;  // ST(0)
                                    arith_operand_b <= temp_operand_b;  // ST(i) or memory
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                // Map comparison results to condition codes
                                status_cc_write <= 1'b1;
                                if (arith_cc_unordered) begin
                                    // Unordered (NaN): C3=1, C2=1, C0=1
                                    status_c3 <= 1'b1;
                                    status_c2 <= 1'b1;
                                    status_c0 <= 1'b1;
                                    // FUCOM does NOT raise invalid exception for NaN
                                end else begin
                                    status_c3 <= arith_cc_equal;
                                    status_c2 <= 1'b0;
                                    status_c0 <= arith_cc_less;
                                end
                                arith_enable <= 1'b0;
                                state <= STATE_STACK_OP;
                            end
                        end

                        INST_FUCOMPP: begin
                            // Unordered compare ST(0) with ST(1) and pop twice
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operation <= 5'd0;  // OP_ADD
                                    arith_operand_a <= temp_operand_a;  // ST(0)
                                    arith_operand_b <= temp_operand_b;  // ST(1)
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                // Set condition codes
                                status_cc_write <= 1'b1;
                                if (arith_cc_unordered) begin
                                    status_c3 <= 1'b1;
                                    status_c2 <= 1'b1;
                                    status_c0 <= 1'b1;
                                end else begin
                                    status_c3 <= arith_cc_equal;
                                    status_c2 <= 1'b0;
                                    status_c0 <= arith_cc_less;
                                end
                                arith_enable <= 1'b0;
                                state <= STATE_STACK_OP;
                            end
                        end

                        default: begin
                            state <= STATE_DONE;
                        end
                    endcase
                end

                STATE_MEM_CONVERT: begin
                    // Memory operand format conversion state
                    // Handles conversions for FLD (load) and FST (store) operations
                    $display("[DEBUG] STATE_MEM_CONVERT: is_load=%b, is_bcd=%b, is_integer=%b, size=%d, arith_enable=%b, arith_done=%b, arith_op=%d",
                            mem_conv_is_load, captured_is_bcd, captured_is_integer, mem_conv_size, arith_enable, arith_done, arith_operation);

                    if (mem_conv_is_load) begin
                        // ===== LOAD OPERATIONS (memory → FP80) =====

                        if (captured_is_bcd) begin
                            // BCD → FP80 (two-stage conversion)
                            if (~mem_conv_stage2) begin
                                // Stage 1: BCD → Binary (uint64)
                                if (~bcd2bin_done) begin
                                    if (~bcd2bin_enable) begin
                                        bcd2bin_bcd_in <= {data_in[79:0]};  // BCD is 80-bit, use data_in directly (stable for BCD)
                                        bcd2bin_enable <= 1'b1;
                                    end
                                end else begin
                                    bcd2bin_enable <= 1'b0;
                                    temp_uint64 <= bcd2bin_binary_out;
                                    mem_conv_stage2 <= 1'b1;  // Move to stage 2
                                end
                            end else begin
                                // Stage 2: Binary → FP80
                                if (~arith_done) begin
                                    if (~arith_enable) begin
                                        arith_operation <= 5'd16;  // OP_UINT64_TO_FP
                                        arith_uint64_in <= temp_uint64;
                                        arith_uint64_sign_in <= 1'b0;  // Positive for now
                                        arith_enable <= 1'b1;
                                    end
                                end else begin
                                    arith_enable <= 1'b0;
                                    temp_result <= arith_result;
                                    mem_conv_active <= 1'b0;
                                    state <= STATE_WRITEBACK;
                                end
                            end
                        end else if (captured_is_integer) begin
                            // Integer → FP80 conversion
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    case (mem_conv_size)
                                        2'd0: begin  // int16 → FP80
                                            arith_operation <= 4'd4;  // OP_INT16_TO_FP
                                            arith_int16_in <= data_in[15:0];
                                        end
                                        2'd1: begin  // int32 → FP80
                                            arith_operation <= 4'd5;  // OP_INT32_TO_FP
                                            arith_int32_in <= data_in[31:0];
                                        end
                                        2'd2: begin  // int64 → FP80 (use uint64 converter)
                                            arith_operation <= 5'd16;  // OP_UINT64_TO_FP
                                            arith_uint64_in <= data_in[63:0];
                                            arith_uint64_sign_in <= 1'b0;  // Sign handling needed
                                        end
                                        default: begin
                                            // Invalid size for integer
                                            error <= 1'b1;
                                            state <= STATE_DONE;
                                        end
                                    endcase
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                arith_enable <= 1'b0;
                                temp_result <= arith_result;
                                mem_conv_active <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end else begin
                            // Float → FP80 conversion
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    $display("[DEBUG] Starting float conversion: size=%d, temp_fp32=%h, op=%d",
                                            mem_conv_size, temp_fp32, (mem_conv_size == 2'd1) ? 4'd8 : 4'd9);
                                    case (mem_conv_size)
                                        2'd1: begin  // FP32 → FP80
                                            arith_operation <= 4'd8;  // OP_FP32_TO_FP80
                                            arith_fp32_in <= temp_fp32;  // Use captured value from STATE_DECODE
                                        end
                                        2'd2: begin  // FP64 → FP80
                                            arith_operation <= 4'd9;  // OP_FP64_TO_FP80
                                            arith_fp64_in <= temp_fp64;  // Use captured value from STATE_DECODE
                                        end
                                        default: begin
                                            // Invalid size for float (word not valid, tbyte already FP80)
                                            error <= 1'b1;
                                            state <= STATE_DONE;
                                        end
                                    endcase
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                $display("[DEBUG] FP load conversion done! arith_result=%h, temp_fp32=%h", arith_result, temp_fp32);
                                arith_enable <= 1'b0;
                                temp_result <= arith_result;
                                mem_conv_active <= 1'b0;
                                state <= STATE_WRITEBACK;
                            end
                        end

                    end else begin
                        // ===== STORE OPERATIONS (FP80 → memory) =====
                        // Always use temp_operand_a which contains ST(0)

                        if (captured_is_bcd) begin
                            // FP80 → BCD (two-stage conversion)
                            if (~mem_conv_stage2) begin
                                // Stage 1: FP80 → uint64
                                if (~arith_done) begin
                                    if (~arith_enable) begin
                                        arith_operation <= 5'd17;  // OP_FP_TO_UINT64
                                        arith_operand_a <= temp_operand_a;
                                        arith_enable <= 1'b1;
                                    end
                                end else begin
                                    arith_enable <= 1'b0;
                                    temp_uint64 <= arith_uint64_out;
                                    mem_conv_stage2 <= 1'b1;  // Move to stage 2
                                end
                            end else begin
                                // Stage 2: uint64 → BCD
                                if (~bin2bcd_done) begin
                                    if (~bin2bcd_enable) begin
                                        bin2bcd_binary_in <= temp_uint64;
                                        bin2bcd_sign_in <= 1'b0;  // For now, assume positive
                                        bin2bcd_enable <= 1'b1;
                                    end
                                end else begin
                                    bin2bcd_enable <= 1'b0;
                                    data_out <= bin2bcd_bcd_out;
                                    mem_conv_active <= 1'b0;
                                    state <= STATE_DONE;
                                end
                            end
                        end else if (captured_is_integer) begin
                            // FP80 → Integer conversion
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operand_a <= temp_operand_a;
                                    case (mem_conv_size)
                                        2'd0: arith_operation <= 4'd6;  // OP_FP_TO_INT16
                                        2'd1: arith_operation <= 4'd7;  // OP_FP_TO_INT32
                                        2'd2: arith_operation <= 5'd17;  // OP_FP_TO_UINT64
                                        default: begin
                                            error <= 1'b1;
                                            state <= STATE_DONE;
                                        end
                                    endcase
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                arith_enable <= 1'b0;
                                case (mem_conv_size)
                                    2'd0: data_out[15:0] <= arith_int16_out;
                                    2'd1: data_out[31:0] <= arith_int32_out;
                                    2'd2: data_out[63:0] <= arith_uint64_out;
                                endcase
                                mem_conv_active <= 1'b0;
                                state <= STATE_DONE;
                            end
                        end else begin
                            // FP80 → Float conversion
                            if (~arith_done) begin
                                if (~arith_enable) begin
                                    arith_operand_a <= temp_operand_a;
                                    case (mem_conv_size)
                                        2'd1: arith_operation <= 4'd10;  // OP_FP80_TO_FP32
                                        2'd2: arith_operation <= 4'd11;  // OP_FP80_TO_FP64
                                        default: begin
                                            error <= 1'b1;
                                            state <= STATE_DONE;
                                        end
                                    endcase
                                    arith_enable <= 1'b1;
                                end
                            end else begin
                                arith_enable <= 1'b0;
                                case (mem_conv_size)
                                    2'd1: data_out[31:0] <= arith_fp32_out;
                                    2'd2: data_out[63:0] <= arith_fp64_out;
                                endcase
                                mem_conv_active <= 1'b0;
                                state <= STATE_DONE;
                            end
                        end
                    end
                end

                STATE_WRITEBACK: begin
                    // No action, just transition
                    state <= STATE_STACK_OP;
                end

                STATE_WAIT_MICROSEQ: begin
                    // Wait for microsequencer to complete BCD operation
                    if (microseq_complete) begin
                        // Microcode execution complete
                        microseq_active <= 1'b0;

                        case (current_inst)
                            INST_FBLD: begin
                                // FBLD: Load BCD → Binary → FP80
                                // Result FP80 value is in microseq_temp_result (microsequencer's temp_result register)
                                temp_result <= microseq_temp_result;
                                state <= STATE_WRITEBACK;
                            end

                            INST_FBSTP: begin
                                // FBSTP: Store FP80 → Binary → BCD and Pop
                                // Result BCD value is in microseq_data_out
                                data_out <= microseq_data_out;
                                state <= STATE_WRITEBACK;
                            end

                            default: begin
                                // Unexpected instruction in microseq wait state
                                error <= 1'b1;
                                state <= STATE_DONE;
                            end
                        endcase
                    end
                    // else: stay in this state and wait
                end

                STATE_STACK_OP: begin
                    case (current_inst)
                        // Load operations: push result onto stack
                        INST_FLD, INST_FILD16, INST_FILD32, INST_FBLD,
                        INST_FLD32, INST_FLD64: begin
                            stack_push <= 1'b1;
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Constant loading: push constant onto stack
                        INST_FLD1, INST_FLDZ, INST_FLDPI, INST_FLDL2E,
                        INST_FLDL2T, INST_FLDLG2, INST_FLDLN2: begin
                            stack_push <= 1'b1;
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Arithmetic operations: write to ST(0)
                        INST_FADD, INST_FSUB, INST_FMUL, INST_FDIV,
                        INST_FSUBR, INST_FDIVR: begin
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Transcendental operations (single result): write to ST(0)
                        INST_FSQRT, INST_FSIN, INST_FCOS, INST_F2XM1: begin
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Trivial operations: write to ST(0)
                        INST_FABS, INST_FCHS: begin
                            stack_write_reg <= 3'd0;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // FXCH: Exchange ST(0) with ST(i)
                        // Implementation (two cycles):
                        //   Cycle 1: Write ST(i) value to ST(0)
                        //   Cycle 2: Write ST(0) value to ST(i)
                        INST_FXCH: begin
                            if (has_secondary_result) begin
                                // Write old ST(i) value to ST(0)
                                stack_write_reg <= 3'd0;
                                stack_data_in <= temp_result;             // old ST(i)
                                stack_write_enable <= 1'b1;
                                state <= STATE_FXCH_WRITE2;  // Go to second write
                            end else begin
                                // Fallback: no exchange needed
                                state <= STATE_DONE;
                            end
                        end

                        // FSINCOS: Special case - returns both sin and cos
                        // Intel 8087 behavior:
                        //   Input:  ST(0) = θ
                        //   Output: ST(0) = cos(θ), ST(1) = sin(θ)
                        // Implementation (two cycles):
                        //   Cycle 1: Write sin(θ) to ST(1)
                        //   Cycle 2: Write cos(θ) to ST(0)
                        INST_FSINCOS: begin
                            if (has_secondary_result) begin
                                // Write sin(θ) to ST(1)
                                stack_write_reg <= 3'd1;
                                stack_data_in <= temp_result;            // sin(θ)
                                stack_write_enable <= 1'b1;
                                state <= STATE_FSINCOS_PUSH;  // Go to second write
                            end else begin
                                // Fallback if no secondary result (shouldn't happen for FSINCOS)
                                stack_write_reg <= 3'd0;
                                stack_data_in <= temp_result;
                                stack_write_enable <= 1'b1;
                                state <= STATE_DONE;
                            end
                        end

                        // FPTAN: Special case - returns tan and 1.0
                        // Intel 8087 behavior:
                        //   Input:  ST(0) = θ
                        //   Output: ST(0) = 1.0, ST(1) = tan(θ)
                        // Implementation (two cycles):
                        //   Cycle 1: Write tan(θ) to ST(1)
                        //   Cycle 2: Write 1.0 to ST(0)
                        INST_FPTAN: begin
                            if (has_secondary_result) begin
                                // Write tan(θ) to ST(1)
                                stack_write_reg <= 3'd1;
                                stack_data_in <= temp_result;            // tan(θ)
                                stack_write_enable <= 1'b1;
                                state <= STATE_FSINCOS_PUSH;  // Reuse same state for second write
                            end else begin
                                // Fallback if no secondary result
                                stack_write_reg <= 3'd0;
                                stack_data_in <= temp_result;
                                stack_write_enable <= 1'b1;
                                state <= STATE_DONE;
                            end
                        end

                        // Arithmetic with pop: write to ST(1) then pop
                        INST_FADDP, INST_FSUBP, INST_FMULP, INST_FDIVP,
                        INST_FSUBRP, INST_FDIVRP,
                        INST_FPATAN, INST_FYL2X, INST_FYL2XP1: begin
                            stack_write_reg <= 3'd1;
                            stack_data_in <= temp_result;
                            stack_write_enable <= 1'b1;
                            stack_pop <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Store and pop
                        INST_FSTP, INST_FISTP16, INST_FISTP32, INST_FBSTP,
                        INST_FSTP32, INST_FSTP64: begin
                            stack_pop <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Compare and pop
                        INST_FCOMP, INST_FUCOMP: begin
                            stack_pop <= 1'b1;
                            state <= STATE_DONE;
                        end

                        // Compare and pop twice
                        INST_FCOMPP, INST_FUCOMPP: begin
                            stack_pop <= 1'b1;
                            // Second pop will be handled by setting a flag
                            state <= STATE_FCOMPP_POP2;
                        end

                        default: begin
                            // No stack operation
                            state <= STATE_DONE;
                        end
                    endcase
                end

                STATE_FSINCOS_PUSH: begin
                    // Second cycle of FSINCOS: write cos(θ) to ST(0)
                    stack_write_reg <= 3'd0;
                    stack_data_in <= temp_result_secondary;  // cos(θ)
                    stack_write_enable <= 1'b1;
                    state <= STATE_DONE;
                end

                STATE_FXCH_WRITE2: begin
                    // Second cycle of FXCH: write old ST(0) value to ST(i)
                    stack_write_reg <= current_index;
                    stack_data_in <= temp_result_secondary;  // old ST(0)
                    stack_write_enable <= 1'b1;
                    state <= STATE_DONE;
                end

                STATE_FCOMPP_POP2: begin
                    // Second pop for FCOMPP
                    stack_pop <= 1'b1;
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
                    arith_operation <= 5'd15;

                    state <= STATE_IDLE;
                end

                default: state <= STATE_IDLE;
            endcase
        end
    end

endmodule
