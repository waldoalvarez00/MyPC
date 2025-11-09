`timescale 1ns / 1ps

//=====================================================================
// Extended MicroSequencer for 8087 FPU
//
// This module extends the basic microsequencer with hardware unit
// interface support. It provides "call and wait" subroutines that
// delegate to existing FPU_Core hardware units:
// - FPU_ArithmeticUnit (add, sub, mul, div, sqrt, trig, conversions)
// - Stack Manager (push, pop, exchange)
// - Format Converters (int, FP, BCD)
//
// Key Design: Microcode sequences operations, hardware units compute
//=====================================================================

module MicroSequencer_Extended (
    input wire clk,
    input wire reset,

    // Control interface
    input wire        start,                // Start microprogram execution
    input wire [3:0]  micro_program_index,  // Which microprogram to run
    output reg        instruction_complete, // Execution complete

    // Data bus interface (for memory operations)
    input wire [79:0] data_in,
    output reg [79:0] data_out,

    // ===== Interfaces to FPU_Core Hardware Units (REUSE EXISTING) =====

    // Interface to FPU_ArithmeticUnit
    output reg [4:0]  arith_operation,      // Operation code
    output reg        arith_enable,         // Start operation
    output reg [1:0]  arith_rounding_mode,  // Rounding mode
    output reg [79:0] arith_operand_a,      // Operand A (80-bit FP)
    output reg [79:0] arith_operand_b,      // Operand B (80-bit FP)
    output reg signed [15:0] arith_int16_in,
    output reg signed [31:0] arith_int32_in,
    output reg [31:0] arith_fp32_in,
    output reg [63:0] arith_fp64_in,
    input wire [79:0] arith_result,         // Result (80-bit FP)
    input wire signed [15:0] arith_int16_out,
    input wire signed [31:0] arith_int32_out,
    input wire [31:0] arith_fp32_out,
    input wire [63:0] arith_fp64_out,
    input wire        arith_done,           // Operation complete
    input wire        arith_cc_less,
    input wire        arith_cc_equal,
    input wire        arith_cc_greater,
    input wire        arith_cc_unordered,

    // Interface to Stack Manager
    output reg        stack_push_req,       // Push request
    output reg        stack_pop_req,        // Pop request
    output reg [2:0]  stack_read_sel,       // Which register to read
    output reg [2:0]  stack_write_sel,      // Which register to write
    output reg        stack_write_en,       // Write enable
    output reg [79:0] stack_write_data,     // Data to write
    input wire [79:0] stack_read_data,      // Data read from stack
    input wire        stack_op_done,        // Stack operation complete

    // Status/Control interface
    input wire [15:0] status_word_in,
    output reg [15:0] status_word_out,
    output reg        status_word_write,
    input wire [15:0] control_word_in,
    output reg [15:0] control_word_out,
    output reg        control_word_write
);

    //=================================================================
    // Opcode Definitions
    //=================================================================

    // Overall opcodes
    localparam OPCODE_NOP    = 4'h0;
    localparam OPCODE_EXEC   = 4'h1;
    localparam OPCODE_JUMP   = 4'h2;
    localparam OPCODE_CALL   = 4'h3;
    localparam OPCODE_RET    = 4'h4;
    localparam OPCODE_HALT   = 4'hF;

    // Basic micro-operations (0x0-0xF)
    localparam MOP_LOAD           = 4'h1;  // Load from data bus
    localparam MOP_STORE          = 4'h2;  // Store to data bus
    localparam MOP_MOVE_TEMP      = 4'h3;  // Move between temp registers
    localparam MOP_LOAD_IMM       = 4'h4;  // Load immediate value

    // Hardware unit call operations (0x10-0x1F) - NEW!
    localparam MOP_CALL_ARITH     = 5'h10; // Start arithmetic operation
    localparam MOP_WAIT_ARITH     = 5'h11; // Wait for arithmetic completion
    localparam MOP_LOAD_ARITH_RES = 5'h12; // Load result from arithmetic unit
    localparam MOP_CALL_STACK     = 5'h13; // Execute stack operation
    localparam MOP_WAIT_STACK     = 5'h14; // Wait for stack completion
    localparam MOP_LOAD_STACK_REG = 5'h15; // Load from stack register
    localparam MOP_STORE_STACK_REG= 5'h16; // Store to stack register
    localparam MOP_SET_STATUS     = 5'h17; // Set status flags
    localparam MOP_GET_STATUS     = 5'h18; // Get status flags
    localparam MOP_GET_CC         = 5'h19; // Get condition codes

    //=================================================================
    // FSM States
    //=================================================================

    localparam STATE_IDLE   = 3'd0;
    localparam STATE_FETCH  = 3'd1;
    localparam STATE_DECODE = 3'd2;
    localparam STATE_EXEC   = 3'd3;
    localparam STATE_WAIT   = 3'd4;  // NEW: Wait for hardware completion

    reg [2:0] state;

    //=================================================================
    // Program Counter and Instruction
    //=================================================================

    reg [15:0] pc;                          // Program counter
    reg [31:0] microinstruction;            // Current instruction

    // Instruction fields
    wire [3:0]  opcode     = microinstruction[31:28];
    wire [4:0]  micro_op   = microinstruction[27:23];  // Extended to 5 bits!
    wire [7:0]  immediate  = microinstruction[22:15];
    wire [14:0] next_addr  = microinstruction[14:0];   // 15-bit address

    //=================================================================
    // Call Stack
    //=================================================================

    reg [15:0] call_stack [0:15];
    reg [3:0]  call_sp;

    //=================================================================
    // Microprogram Table
    //=================================================================

    reg [15:0] micro_program_table [0:15];
    initial begin
        // Program 0: FADD subroutine
        micro_program_table[0]  = 16'd0x0100;
        // Program 1: FSUB subroutine
        micro_program_table[1]  = 16'd0x0110;
        // Program 2: FMUL subroutine
        micro_program_table[2]  = 16'd0x0120;
        // Program 3: FDIV subroutine
        micro_program_table[3]  = 16'd0x0130;
        // Program 4: FSQRT subroutine
        micro_program_table[4]  = 16'd0x0140;
        // Program 5: FSIN subroutine
        micro_program_table[5]  = 16'd0x0150;
        // Program 6: FCOS subroutine
        micro_program_table[6]  = 16'd0x0160;
        // Program 7: FLD (with format conversion)
        micro_program_table[7]  = 16'd0x0200;
        // Program 8: FST (with format conversion)
        micro_program_table[8]  = 16'd0x0210;
        // Remaining slots for complex operations
        micro_program_table[9]  = 16'd0x0300;  // Reserved for FPREM
        micro_program_table[10] = 16'd0x0400;  // Reserved for FXTRACT
        micro_program_table[11] = 16'd0x0500;  // Reserved for FSCALE
    end

    //=================================================================
    // Temporary Registers
    //=================================================================

    reg [79:0] temp_fp_a;       // Operand A (80-bit FP)
    reg [79:0] temp_fp_b;       // Operand B (80-bit FP)
    reg [79:0] temp_result;     // Result storage
    reg [63:0] temp_reg;        // General purpose temp
    reg [31:0] loop_reg;        // Loop counter
    reg [2:0]  temp_stack_idx;  // Stack index

    //=================================================================
    // Wait State Control
    //=================================================================

    reg waiting_for_arith;      // Waiting for arithmetic unit
    reg waiting_for_stack;      // Waiting for stack operation

    //=================================================================
    // Microcode ROM (4096 x 32-bit)
    //=================================================================

    reg [31:0] microcode_rom [0:4095];

    //=================================================================
    // Microcode Programs - Subroutine Library
    //=================================================================

    initial begin
        //-------------------------------------------------------------
        // Program 0: FADD - Floating Point Addition
        // Address: 0x0100-0x0107
        // Assumes: operands already in temp_fp_a, temp_fp_b
        // Returns: result in temp_result
        //-------------------------------------------------------------
        microcode_rom[16'h0100] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd0, 15'h0101};      // Call ADD (op=0)
        microcode_rom[16'h0101] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0101};      // Wait (loop here)
        microcode_rom[16'h0102] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0103};  // Load result
        microcode_rom[16'h0103] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return

        //-------------------------------------------------------------
        // Program 1: FSUB - Floating Point Subtraction
        // Address: 0x0110-0x0113
        //-------------------------------------------------------------
        microcode_rom[16'h0110] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd1, 15'h0111};      // Call SUB (op=1)
        microcode_rom[16'h0111] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0111};      // Wait
        microcode_rom[16'h0112] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0113};  // Load result
        microcode_rom[16'h0113] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return

        //-------------------------------------------------------------
        // Program 2: FMUL - Floating Point Multiplication
        // Address: 0x0120-0x0123
        //-------------------------------------------------------------
        microcode_rom[16'h0120] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd2, 15'h0121};      // Call MUL (op=2)
        microcode_rom[16'h0121] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0121};      // Wait
        microcode_rom[16'h0122] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0123};  // Load result
        microcode_rom[16'h0123] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return

        //-------------------------------------------------------------
        // Program 3: FDIV - Floating Point Division
        // Address: 0x0130-0x0133
        //-------------------------------------------------------------
        microcode_rom[16'h0130] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd3, 15'h0131};      // Call DIV (op=3)
        microcode_rom[16'h0131] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0131};      // Wait
        microcode_rom[16'h0132] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0133};  // Load result
        microcode_rom[16'h0133] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return

        //-------------------------------------------------------------
        // Program 4: FSQRT - Square Root
        // Address: 0x0140-0x0143
        //-------------------------------------------------------------
        microcode_rom[16'h0140] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd12, 15'h0141};     // Call SQRT (op=12)
        microcode_rom[16'h0141] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0141};      // Wait
        microcode_rom[16'h0142] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0143};  // Load result
        microcode_rom[16'h0143] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return

        //-------------------------------------------------------------
        // Program 5: FSIN - Sine
        // Address: 0x0150-0x0153
        //-------------------------------------------------------------
        microcode_rom[16'h0150] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd13, 15'h0151};     // Call SIN (op=13)
        microcode_rom[16'h0151] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0151};      // Wait
        microcode_rom[16'h0152] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0153};  // Load result
        microcode_rom[16'h0153] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return

        //-------------------------------------------------------------
        // Program 6: FCOS - Cosine
        // Address: 0x0160-0x0163
        //-------------------------------------------------------------
        microcode_rom[16'h0160] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd14, 15'h0161};     // Call COS (op=14)
        microcode_rom[16'h0161] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0161};      // Wait
        microcode_rom[16'h0162] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0163};  // Load result
        microcode_rom[16'h0163] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return

        //-------------------------------------------------------------
        // Initialize rest of ROM to HALT
        //-------------------------------------------------------------
        integer i;
        for (i = 0; i < 4096; i = i + 1) begin
            if (microcode_rom[i] == 32'h0) begin
                microcode_rom[i] = {OPCODE_HALT, 5'd0, 8'd0, 15'd0};
            end
        end
    end

    //=================================================================
    // Main State Machine
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_IDLE;
            pc <= 16'd0;
            call_sp <= 4'd0;
            instruction_complete <= 1'b0;

            // Reset temp registers
            temp_fp_a <= 80'd0;
            temp_fp_b <= 80'd0;
            temp_result <= 80'd0;
            temp_reg <= 64'd0;
            loop_reg <= 32'd0;
            temp_stack_idx <= 3'd0;

            // Reset hardware unit interfaces
            arith_enable <= 1'b0;
            arith_operation <= 5'd0;
            arith_rounding_mode <= 2'd0;
            arith_operand_a <= 80'd0;
            arith_operand_b <= 80'd0;
            arith_int16_in <= 16'd0;
            arith_int32_in <= 32'd0;
            arith_fp32_in <= 32'd0;
            arith_fp64_in <= 64'd0;

            stack_push_req <= 1'b0;
            stack_pop_req <= 1'b0;
            stack_read_sel <= 3'd0;
            stack_write_sel <= 3'd0;
            stack_write_en <= 1'b0;
            stack_write_data <= 80'd0;

            status_word_out <= 16'd0;
            status_word_write <= 1'b0;
            control_word_out <= 16'd0;
            control_word_write <= 1'b0;

            data_out <= 80'd0;

            waiting_for_arith <= 1'b0;
            waiting_for_stack <= 1'b0;

        end else begin
            // Default: clear pulse signals
            arith_enable <= 1'b0;
            stack_push_req <= 1'b0;
            stack_pop_req <= 1'b0;
            stack_write_en <= 1'b0;
            status_word_write <= 1'b0;
            control_word_write <= 1'b0;

            case (state)
                STATE_IDLE: begin
                    if (start) begin
                        pc <= micro_program_table[micro_program_index];
                        instruction_complete <= 1'b0;
                        call_sp <= 4'd0;
                        waiting_for_arith <= 1'b0;
                        waiting_for_stack <= 1'b0;
                        state <= STATE_FETCH;
                    end
                end

                STATE_FETCH: begin
                    microinstruction <= microcode_rom[pc];
                    state <= STATE_DECODE;
                end

                STATE_DECODE: begin
                    state <= STATE_EXEC;
                end

                STATE_EXEC: begin
                    case (opcode)
                        OPCODE_NOP: begin
                            pc <= pc + 1;
                            state <= STATE_FETCH;
                        end

                        OPCODE_EXEC: begin
                            case (micro_op)
                                //-------------------------------------
                                // Basic Operations
                                //-------------------------------------
                                MOP_LOAD: begin
                                    temp_result <= data_in;
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                MOP_STORE: begin
                                    data_out <= temp_result;
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                //-------------------------------------
                                // Arithmetic Unit Operations
                                //-------------------------------------
                                MOP_CALL_ARITH: begin
                                    // Start arithmetic operation
                                    arith_operation <= immediate[4:0];
                                    arith_operand_a <= temp_fp_a;
                                    arith_operand_b <= temp_fp_b;
                                    arith_enable <= 1'b1;
                                    waiting_for_arith <= 1'b1;
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                MOP_WAIT_ARITH: begin
                                    if (arith_done) begin
                                        // Arithmetic complete
                                        waiting_for_arith <= 1'b0;
                                        pc <= {1'b0, next_addr};
                                        state <= STATE_FETCH;
                                    end else begin
                                        // Keep waiting (stay at current PC)
                                        pc <= pc;
                                        state <= STATE_FETCH;
                                    end
                                end

                                MOP_LOAD_ARITH_RES: begin
                                    temp_result <= arith_result;
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                //-------------------------------------
                                // Stack Operations
                                //-------------------------------------
                                MOP_LOAD_STACK_REG: begin
                                    stack_read_sel <= immediate[2:0];
                                    temp_result <= stack_read_data;  // Combinational read
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                MOP_STORE_STACK_REG: begin
                                    stack_write_sel <= immediate[2:0];
                                    stack_write_data <= temp_result;
                                    stack_write_en <= 1'b1;
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                //-------------------------------------
                                // Status/Control Operations
                                //-------------------------------------
                                MOP_GET_STATUS: begin
                                    temp_reg <= {48'd0, status_word_in};
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                MOP_SET_STATUS: begin
                                    status_word_out <= temp_reg[15:0];
                                    status_word_write <= 1'b1;
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                MOP_GET_CC: begin
                                    // Pack condition codes into temp_reg
                                    temp_reg[0] <= arith_cc_less;
                                    temp_reg[1] <= arith_cc_equal;
                                    temp_reg[2] <= arith_cc_greater;
                                    temp_reg[3] <= arith_cc_unordered;
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end

                                default: begin
                                    pc <= {1'b0, next_addr};
                                    state <= STATE_FETCH;
                                end
                            endcase
                        end

                        OPCODE_JUMP: begin
                            pc <= {1'b0, next_addr};
                            state <= STATE_FETCH;
                        end

                        OPCODE_CALL: begin
                            call_stack[call_sp] <= pc + 1;
                            call_sp <= call_sp + 1;
                            pc <= {1'b0, next_addr};
                            state <= STATE_FETCH;
                        end

                        OPCODE_RET: begin
                            if (call_sp > 0) begin
                                call_sp <= call_sp - 1;
                                pc <= call_stack[call_sp - 1];
                            end else begin
                                pc <= 16'd0;  // Error: empty call stack
                            end
                            state <= STATE_FETCH;
                        end

                        OPCODE_HALT: begin
                            instruction_complete <= 1'b1;
                            state <= STATE_IDLE;
                        end

                        default: begin
                            pc <= pc + 1;
                            state <= STATE_FETCH;
                        end
                    endcase
                end

                default: state <= STATE_IDLE;
            endcase
        end
    end

endmodule
