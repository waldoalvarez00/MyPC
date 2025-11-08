`timescale 1ns / 1ps

//---------------------------------------------------------------------
// Opcode definitions for overall microinstruction type.
`define OPCODE_NOP    4'h0
`define OPCODE_EXEC   4'h1
`define OPCODE_JUMP   4'h2
`define OPCODE_CALL   4'h3
`define OPCODE_RET    4'h4
`define OPCODE_HALT   4'hF

//---------------------------------------------------------------------
// Micro–operation codes (4-bit) used in EXEC microinstructions.
`define MOP_LOAD           4'h1  // Load from CPU bus into temp_reg.
`define MOP_STORE          4'h2  // Store from temp_reg to CPU bus.
`define MOP_SET_CONST      4'h3  // Set the math constant index (immediate).
`define MOP_ACCESS_CONST   4'h4  // Load a math constant from ROM into temp_fp.
`define MOP_ADD_SUB        4'h5  // Perform FP addition/subtraction.
`define MOP_SHIFT_LEFT_BIT 4'h6  // Shift temp_reg left by immediate (lower 3 bits).
`define MOP_LOOP_INIT      4'h7  // Initialize the loop register with immediate value.
`define MOP_LOOP_DEC       4'h8  // Decrement loop register and jump if nonzero.
`define MOP_ABS            4'h9  // Compute absolute value of temp_fp.
`define MOP_ROUND          4'hA  // Round temp_fp using rounding mode (immediate lower 2 bits).
`define MOP_NORMALIZE      4'hB  // Normalize temp_fp.

//---------------------------------------------------------------------
// MicroSequencer module definition.
module MicroSequencer (
    input         clk,
    input         reset,
    input         start,               // Signal to start microprogram execution.
    input  [3:0]  micro_program_index, // Index into the microprogram table.
    input  [63:0] cpu_data_in,         // Data from CPU bus (memory load).
    output reg [63:0] cpu_data_out,      // Data to CPU bus (memory store).
    output reg    instruction_complete   // Signals when the microprogram (instruction) is done.
);

    // FSM states.
    localparam STATE_IDLE   = 3'd0;
    localparam STATE_FETCH  = 3'd1;
    localparam STATE_DECODE = 3'd2;
    localparam STATE_EXEC   = 3'd3;

    reg [2:0] state;

    // Microprogram Counter (points into the microcode ROM).
    reg [15:0] pc;

    // Microinstruction format: { opcode[31:28], micro_op[27:24], immediate[23:16], next_addr[15:0] }.
    reg [31:0] microinstruction;
    wire [3:0] opcode     = microinstruction[31:28];
    wire [3:0] micro_op   = microinstruction[27:24];
    wire [7:0] immediate  = microinstruction[23:16];
    wire [15:0] next_addr = microinstruction[15:0];

    // Call stack for micro–code subroutine calls (depth = 4).
    reg [15:0] call_stack [0:3];
    reg [1:0] call_sp;

    // Loop register for for–loops.
    reg [31:0] loop_reg;

    // Temporary registers.
    reg [63:0] temp_reg;         // For general-purpose temporary storage.
    reg [4:0]  math_const_index;  // Used to index the math constants ROM.
    reg [79:0] temp_fp;          // Temporary 80-bit FP register.
    reg [79:0] temp_fp_a, temp_fp_b; // Operands for the FP Add/Sub unit.

    //-----------------------------------------------------------------
    // Microprogram table: maps a 4-bit index to a starting address.
    reg [15:0] micro_program_table [0:15];
    initial begin
        micro_program_table[0] = 16'd0;   // e.g., tangent routine.
        micro_program_table[1] = 16'd10;  // e.g., square-root routine.
        // ... additional mappings as needed.
    end

    //-----------------------------------------------------------------
    // Microcode ROM: 256 x 32-bit microinstructions.
    // Microinstruction fields are:
    //   opcode | micro_op | immediate | next_addr
    reg [31:0] microcode_rom [0:255];
    initial begin
        // Example microprogram sequence:
        // 0: LOAD from CPU bus into temp_reg.
        microcode_rom[0] = {`OPCODE_EXEC, `MOP_LOAD, 8'd0, 16'd1};
        // 1: SET_CONST – load constant index (immediate = 5) into math_const_index.
        microcode_rom[1] = {`OPCODE_EXEC, `MOP_SET_CONST, 8'd5, 16'd2};
        // 2: ACCESS_CONST – load constant from ROM into temp_fp.
        microcode_rom[2] = {`OPCODE_EXEC, `MOP_ACCESS_CONST, 8'd0, 16'd3};
        // 3: STORE – send temp_reg to CPU bus.
        microcode_rom[3] = {`OPCODE_EXEC, `MOP_STORE, 8'd0, 16'd4};
        // 4: HALT – finish the microprogram.
        microcode_rom[4] = {`OPCODE_HALT, 4'd0, 8'd0, 16'd0};

        // Example loop microprogram:
        // 5: LOOP_INIT – load loop_reg with immediate (e.g., 3 iterations).
        microcode_rom[5] = {`OPCODE_EXEC, `MOP_LOOP_INIT, 8'd3, 16'd6};
        // 6: ADD_SUB – perform an FP add/sub (using temp_fp_a and temp_fp_b).
        microcode_rom[6] = {`OPCODE_EXEC, `MOP_ADD_SUB, 8'd0, 16'd7};
        // 7: LOOP_DEC – decrement loop_reg and, if not zero, jump back to address 6.
        microcode_rom[7] = {`OPCODE_EXEC, `MOP_LOOP_DEC, 8'd0, 16'd6};
        // 8: HALT – exit the loop.
        microcode_rom[8] = {`OPCODE_HALT, 4'd0, 8'd0, 16'd0};

        // Additional microinstructions can be defined here...
    end

    //-----------------------------------------------------------------
    // Instantiate the math constants ROM.
    wire [79:0] math_const_out;
    mathconstantsrom_32x80bits mathconst_rom_inst (
        .address(math_const_index),
        .data(math_const_out)
    );

    //-----------------------------------------------------------------
    // Instantiate the FPU Add/Sub unit.
    wire [79:0] addsub_result;
    wire cmp_equal, cmp_less, cmp_greater;
    reg fpu_invert_operand_b;
    FPU_AddSub_Comp_Unit fpu_addsub_inst (
        .clk(clk),
        .invert_operand_b(fpu_invert_operand_b),
        .operand_a(operand_a),
        .operand_b(operand_b),
        .result(addsub_result),
        .cmp_equal(cmp_equal),
        .cmp_less(cmp_less),
        .cmp_greater(cmp_greater)
    );
    // Registers for FPU Add/Sub unit inputs.
    reg [79:0] operand_a, operand_b;

    //-----------------------------------------------------------------
    // Instantiate a bit shifter for left shifts.
    wire [63:0] shift_left_out;
    reg [63:0] shift_left_in;
    reg [2:0] shift_left_amount;
    multiplexer_based_bit_shifter_left shift_left_inst (
        .data_in(shift_left_in),
        .shift_amount(shift_left_amount),
        .data_out(shift_left_out)
    );

    //-----------------------------------------------------------------
    // Instantiate the FPU Absolute Value unit.
    wire [79:0] abs_result;
    FPU_ABS_Unit abs_inst (
        .in(temp_fp),
        .out(abs_result)
    );

    //-----------------------------------------------------------------
    // Instantiate the IEEE754 Rounding unit (extended precision).
    wire [79:0] round_result;
    reg [1:0] rounding_mode;
    ieee754_rounding_unit_extended round_inst (
        .clk(clk),
        .in(temp_fp),
        .mode(rounding_mode),
        .out(round_result)
    );

    //-----------------------------------------------------------------
    // Instantiate the IEEE754 Normalizer (extended precision).
    wire [79:0] norm_result;
    ieee754_normalizer_extended_precision norm_inst (
        .clk(clk),
        .ieee754_in(temp_fp),
        .ieee754_out(norm_result)
    );

    //-----------------------------------------------------------------
    // Main FSM: fetch, decode, and execute microinstructions.
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state                <= STATE_IDLE;
            instruction_complete <= 1'b0;
            pc                   <= 16'd0;
            call_sp              <= 2'd0;
            cpu_data_out         <= 64'd0;
            temp_reg             <= 64'd0;
            loop_reg             <= 32'd0;
            math_const_index     <= 5'd0;
            temp_fp              <= 80'd0;
            temp_fp_a            <= 80'd0;
            temp_fp_b            <= 80'd0;
            fpu_invert_operand_b <= 1'b0;
            operand_a            <= 80'd0;
            operand_b            <= 80'd0;
            shift_left_in        <= 64'd0;
            shift_left_amount    <= 3'd0;
            rounding_mode        <= 2'd0;
        end else begin
            case (state)
                STATE_IDLE: begin
                    if (start) begin
                        // Lookup the starting address from the microprogram table.
                        pc <= micro_program_table[micro_program_index];
                        instruction_complete <= 1'b0;
                        call_sp <= 2'd0;
                        state <= STATE_FETCH;
                    end
                end

                STATE_FETCH: begin
                    // Fetch the current microinstruction from ROM.
                    microinstruction <= microcode_rom[pc];
                    state <= STATE_DECODE;
                end

                STATE_DECODE: begin
                    // (Additional decoding could be done here.)
                    state <= STATE_EXEC;
                end

                STATE_EXEC: begin
                    case (opcode)
                        `OPCODE_NOP: begin
                            pc <= pc + 1;
                        end

                        `OPCODE_EXEC: begin
                            case (micro_op)
                                `MOP_LOAD: begin
                                    // Load a value from the CPU bus into temp_reg.
                                    temp_reg <= cpu_data_in;
                                    pc <= next_addr;
                                end

                                `MOP_STORE: begin
                                    // Store the value from temp_reg to the CPU bus.
                                    cpu_data_out <= temp_reg;
                                    pc <= next_addr;
                                end

                                `MOP_SET_CONST: begin
                                    // Set the math constant index using the immediate value.
                                    math_const_index <= immediate[4:0]; // lower 5 bits used.
                                    pc <= next_addr;
                                end

                                `MOP_ACCESS_CONST: begin
                                    // Access the math constants ROM; result stored in temp_fp.
                                    temp_fp <= math_const_out;
                                    pc <= next_addr;
                                end

                                `MOP_ADD_SUB: begin
                                    // Perform FP add/sub using the FPU Add/Sub unit.
                                    // Use immediate[0] as a flag: 0 = add, 1 = subtract.
                                    fpu_invert_operand_b <= immediate[0];
                                    operand_a <= temp_fp_a;  // Assumes temp_fp_a is preloaded.
                                    operand_b <= temp_fp_b;  // Assumes temp_fp_b is preloaded.
                                    temp_fp <= addsub_result; // Result captured on next clock.
                                    pc <= next_addr;
                                end

                                `MOP_SHIFT_LEFT_BIT: begin
                                    // Shift temp_reg left by the amount in immediate (lower 3 bits).
                                    shift_left_amount <= immediate[2:0];
                                    shift_left_in <= temp_reg;
                                    temp_reg <= shift_left_out;
                                    pc <= next_addr;
                                end

                                `MOP_LOOP_INIT: begin
                                    // Initialize the loop register with the immediate value.
                                    loop_reg <= {24'd0, immediate};
                                    pc <= next_addr;
                                end

                                `MOP_LOOP_DEC: begin
                                    // Decrement loop_reg and, if nonzero, jump to next_addr.
                                    if (loop_reg != 0) begin
                                        loop_reg <= loop_reg - 1;
                                        pc <= next_addr;  // Jump back (loop iteration).
                                    end else begin
                                        pc <= pc + 1;     // Loop finished; continue sequentially.
                                    end
                                end

                                `MOP_ABS: begin
                                    // Compute the absolute value of temp_fp.
                                    temp_fp <= abs_result;
                                    pc <= next_addr;
                                end

                                `MOP_ROUND: begin
                                    // Round temp_fp using the rounding mode in immediate (lower 2 bits).
                                    rounding_mode <= immediate[1:0];
                                    temp_fp <= round_result;
                                    pc <= next_addr;
                                end

                                `MOP_NORMALIZE: begin
                                    // Normalize temp_fp.
                                    temp_fp <= norm_result;
                                    pc <= next_addr;
                                end

                                default: begin
                                    // Unrecognized micro-op: simply advance.
                                    pc <= next_addr;
                                end
                            endcase
                        end

                        `OPCODE_JUMP: begin
                            pc <= next_addr;
                        end

                        `OPCODE_CALL: begin
                            // Push return address onto the call stack and jump.
                            call_stack[call_sp] <= pc + 1;
                            call_sp <= call_sp + 1;
                            pc <= next_addr;
                        end

                        `OPCODE_RET: begin
                            // Pop the return address from the call stack.
                            if (call_sp > 0) begin
                                call_sp <= call_sp - 1;
                                pc <= call_stack[call_sp - 1];
                            end else begin
                                pc <= 16'd0; // Error: empty call stack.
                            end
                        end

                        `OPCODE_HALT: begin
                            instruction_complete <= 1'b1;
                            state <= STATE_IDLE;
                        end

                        default: begin
                            pc <= next_addr;
                        end
                    endcase
                    // Unless HALT, return to fetching the next microinstruction.
                    if (opcode != `OPCODE_HALT)
                        state <= STATE_FETCH;
                end

                default: state <= STATE_IDLE;
            endcase
        end
    end

endmodule
