// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// Unified Intel 8087 FPU Module
//
// Complete production-ready 8087 FPU implementation combining:
// - FPU_Instruction_Decoder: Real D8-DF opcode decoding
// - FPU_Outer_Queue: 4-entry instruction queue for async operation
// - FPU_Core_Async: Async execution with internal instruction queue
// - FPU_Core: Complete execution engine with all arithmetic units
//   * FPU_ArithmeticUnit (IEEE 754 AddSub, MulDiv, Transcendental)
//   * MicroSequencer_Extended_BCD
//   * FPU_Exception_Handler
//   * FPU_RegisterStack (8 × 80-bit registers)
//   * FPU_ControlWord, FPU_StatusWord
//
// Architecture: Authentic 8087 with dual-queue async design
// - Outer Queue: Buffers instructions+EA for memory operation serialization
// - Inner Queue: Arithmetic operation pipelining (FPU_Core_Async)
// - Memory Interface: Direct memory access for memory operands
//
// CPU provides effective address via cpu_fpu_ea when memory operand detected.
// FPU queues instruction+EA, then processes asynchronously while CPU continues.
//
// Date: 2025-11-13
//=====================================================================

module FPU8087(
    // Clock and Reset
    input wire clk,
    input wire reset,

    // ========== CPU Side Interface ==========

    // Instruction Interface - D8-DF ESC Instructions
    input wire        cpu_fpu_instr_valid,    // CPU signals valid FPU instruction
    input wire [7:0]  cpu_fpu_opcode,         // ESC opcode (D8h-DFh)
    input wire [7:0]  cpu_fpu_modrm,          // ModR/M byte
    output wire       cpu_fpu_instr_ack,      // FPU acknowledges instruction

    // Effective Address Interface (for memory operands)
    input wire [19:0] cpu_fpu_ea,             // Effective address from CPU
    input wire        cpu_fpu_ea_valid,       // EA valid (for memory operands)

    // ========== Memory Interface (Direct Access) ==========
    // FPU accesses memory directly for memory operands (authentic 8087 behavior)
    // CPU provides effective address, FPU performs the memory operation
    // Arbiter ensures cache coherency (DMA > FPU > CPU priority)

    output wire [19:0] mem_addr,              // Memory address (byte addressing)
    input wire [15:0]  mem_data_in,           // Data from memory (16-bit bus)
    output wire [15:0] mem_data_out,          // Data to memory
    output wire        mem_access,            // Memory access request
    input wire         mem_ack,               // Memory access acknowledged
    output wire        mem_wr_en,             // Write enable
    output wire [1:0]  mem_bytesel,           // Byte select (11=word, 10=high, 01=low)

    // ========== Status and Control ==========

    output wire       cpu_fpu_busy,           // FPU busy executing (queue not empty or processing)
    output wire [15:0] cpu_fpu_status_word,   // FPU status word (FSTSW)
    input wire [15:0] cpu_fpu_control_word,   // FPU control word (FLDCW)
    input wire        cpu_fpu_ctrl_write,     // Write control word
    output wire       cpu_fpu_exception,      // Unmasked exception occurred
    output wire       cpu_fpu_irq             // Interrupt request (8087 INT)
);

    //=================================================================
    // Instruction Decoder Signals
    //=================================================================

    wire [15:0] instruction_word;
    wire [7:0]  decoded_opcode;
    wire [2:0]  decoded_stack_index;
    wire        decoded_has_memory_op;
    wire        decoded_has_pop;
    wire        decoded_has_push;
    wire [1:0]  decoded_operand_size;
    wire        decoded_is_integer;
    wire        decoded_is_bcd;
    wire        decoded_valid;

    // Combine opcode and ModR/M into 16-bit instruction word
    assign instruction_word = {cpu_fpu_opcode, cpu_fpu_modrm};

    //=================================================================
    // FPU Instruction Decoder (D8-DF → Internal Opcodes)
    //=================================================================

    FPU_Instruction_Decoder decoder (
        .instruction(instruction_word),
        .decode(cpu_fpu_instr_valid),

        // Decoded outputs
        .internal_opcode(decoded_opcode),
        .stack_index(decoded_stack_index),
        .has_memory_op(decoded_has_memory_op),
        .has_pop(decoded_has_pop),
        .has_push(decoded_has_push),
        .operand_size(decoded_operand_size),
        .is_integer(decoded_is_integer),
        .is_bcd(decoded_is_bcd),
        .valid(decoded_valid),
        .uses_st0_sti(),  // Not used
        .uses_sti_st0()   // Not used
    );

    //=================================================================
    // FPU Outer Queue (Instruction+EA Buffering)
    //=================================================================

    reg         queue_enqueue;
    reg         queue_dequeue;
    wire        queue_full;
    wire        queue_empty;
    wire [2:0]  queue_count;

    wire [7:0]  queued_opcode;
    wire [2:0]  queued_stack_index;
    wire [19:0] queued_ea;
    wire [1:0]  queued_operand_size;
    wire        queued_is_integer;
    wire        queued_is_bcd;
    wire        queued_has_memory_op;
    wire        queued_has_pop;

    FPU_Outer_Queue outer_queue (
        .clk(clk),
        .reset(reset),

        // Enqueue from CPU
        .enqueue(queue_enqueue),
        .opcode_in(decoded_opcode),
        .stack_index_in(decoded_stack_index),
        .ea_in(cpu_fpu_ea),
        .operand_size_in(decoded_operand_size),
        .is_integer_in(decoded_is_integer),
        .is_bcd_in(decoded_is_bcd),
        .has_memory_op_in(decoded_has_memory_op),
        .has_pop_in(decoded_has_pop),
        .queue_full(queue_full),

        // Dequeue to execution
        .dequeue(queue_dequeue),
        .opcode_out(queued_opcode),
        .stack_index_out(queued_stack_index),
        .ea_out(queued_ea),
        .operand_size_out(queued_operand_size),
        .is_integer_out(queued_is_integer),
        .is_bcd_out(queued_is_bcd),
        .has_memory_op_out(queued_has_memory_op),
        .has_pop_out(queued_has_pop),
        .queue_empty(queue_empty),
        .queue_count(queue_count)
    );

    //=================================================================
    // Memory Interface State Machine
    //=================================================================

    localparam MEM_IDLE     = 3'd0;
    localparam MEM_READ     = 3'd1;
    localparam MEM_WRITE    = 3'd2;
    localparam MEM_COMPLETE = 3'd3;

    reg [2:0]  mem_state;
    reg [19:0] mem_addr_reg;
    reg [15:0] mem_data_out_reg;
    reg        mem_access_reg;
    reg        mem_wr_en_reg;
    reg [1:0]  mem_bytesel_reg;
    reg [79:0] mem_operand_buffer;
    reg [3:0]  mem_transfer_count;      // For multi-word transfers (80-bit = 5 words)
    reg        mem_operation_complete;

    //=================================================================
    // Interface Control State Machine
    //=================================================================

    localparam STATE_IDLE       = 4'd0;
    localparam STATE_MEM_LOAD   = 4'd2;
    localparam STATE_EXECUTE    = 4'd3;
    localparam STATE_MEM_STORE  = 4'd4;
    localparam STATE_RESULT     = 4'd5;

    reg [3:0] state;

    // Instruction context registers (from queue)
    reg [7:0]  current_opcode;
    reg [2:0]  current_stack_index;
    reg        current_has_memory_op;
    reg [1:0]  current_operand_size;
    reg        current_is_integer;
    reg        current_is_bcd;
    reg        needs_mem_load;
    reg        needs_mem_store;

    // Data buffering
    reg [79:0] operand_buffer;
    reg [79:0] result_buffer;
    reg        internal_busy;
    reg        instruction_ack;

    //=================================================================
    // FPU Core Async Signals
    //=================================================================

    wire        core_ready;
    wire        core_error;
    wire [79:0] core_data_out;
    wire [31:0] core_int_data_out;
    wire [15:0] core_status_out;
    wire [15:0] core_control_out;
    wire [15:0] core_tag_word_out;
    wire        core_busy;
    wire        core_int_request;

    reg         core_execute;
    reg  [79:0] core_data_in;
    reg  [31:0] core_int_data_in;

    //=================================================================
    // FPU Core Async (Inner Queue + Core)
    //=================================================================

    FPU_Core_Async fpu_core_async (
        .clk(clk),
        .reset(reset),

        // Instruction interface (simplified opcodes from queue)
        .instruction(current_opcode),
        .stack_index(current_stack_index),
        .execute(core_execute),
        .ready(core_ready),
        .error(core_error),

        // Data interface
        .data_in(core_data_in),
        .data_out(core_data_out),
        .int_data_in(core_int_data_in),
        .int_data_out(core_int_data_out),

        // Memory operand format information
        .has_memory_op(current_has_memory_op),
        .operand_size(current_operand_size),
        .is_integer(current_is_integer),
        .is_bcd(current_is_bcd),

        // Control/Status interface
        .control_in(cpu_fpu_control_word),
        .control_write(cpu_fpu_ctrl_write),
        .status_out(core_status_out),
        .control_out(core_control_out),
        .tag_word_out(core_tag_word_out),

        // Asynchronous operation signals
        .busy(core_busy),
        .int_request(core_int_request)
    );

    //=================================================================
    // Memory Interface Control
    //=================================================================

    always @(posedge clk) begin
        if (reset) begin
            mem_state <= MEM_IDLE;
            mem_addr_reg <= 20'h0;
            mem_data_out_reg <= 16'h0;
            mem_access_reg <= 1'b0;
            mem_wr_en_reg <= 1'b0;
            mem_bytesel_reg <= 2'b11;
            mem_operand_buffer <= 80'h0;
            mem_transfer_count <= 4'h0;
            mem_operation_complete <= 1'b0;
        end else begin
            case (mem_state)
                MEM_IDLE: begin
                    mem_operation_complete <= 1'b0;
                    mem_access_reg <= 1'b0;

                    // Start memory read/write operation
                    if (needs_mem_load && (state == STATE_MEM_LOAD)) begin
                        mem_state <= MEM_READ;
                        mem_transfer_count <= 4'h0;
                        mem_operand_buffer <= 80'h0;
                    end else if (needs_mem_store && (state == STATE_MEM_STORE)) begin
                        mem_state <= MEM_WRITE;
                        mem_transfer_count <= 4'h0;
                        mem_operand_buffer <= result_buffer;
                    end
                end

                MEM_READ: begin
                    // Multi-word memory read (16-bit bus, up to 80-bit operands)
                    mem_access_reg <= 1'b1;
                    mem_wr_en_reg <= 1'b0;
                    mem_bytesel_reg <= 2'b11;  // Word access

                    // Address calculation: base + word_offset
                    if (mem_transfer_count == 0) begin
                        mem_addr_reg <= mem_addr_reg;  // Use captured EA
                    end else begin
                        mem_addr_reg <= mem_addr_reg + 2;  // Increment by 2 bytes
                    end

                    if (mem_ack) begin
                        // Store received word
                        case (mem_transfer_count)
                            4'h0: mem_operand_buffer[15:0]   <= mem_data_in;
                            4'h1: mem_operand_buffer[31:16]  <= mem_data_in;
                            4'h2: mem_operand_buffer[47:32]  <= mem_data_in;
                            4'h3: mem_operand_buffer[63:48]  <= mem_data_in;
                            4'h4: mem_operand_buffer[79:64]  <= mem_data_in;
                        endcase

                        mem_transfer_count <= mem_transfer_count + 1;

                        // Determine how many words to transfer based on operand size
                        if ((current_operand_size == 2'b00 && mem_transfer_count >= 0) ||  // 16-bit (1 word)
                            (current_operand_size == 2'b01 && mem_transfer_count >= 1) ||  // 32-bit (2 words)
                            (current_operand_size == 2'b10 && mem_transfer_count >= 3) ||  // 64-bit (4 words)
                            (current_operand_size == 2'b11 && mem_transfer_count >= 4)) begin // 80-bit (5 words)
                            mem_state <= MEM_COMPLETE;
                            mem_access_reg <= 1'b0;
                        end
                    end
                end

                MEM_WRITE: begin
                    // Multi-word memory write
                    mem_access_reg <= 1'b1;
                    mem_wr_en_reg <= 1'b1;
                    mem_bytesel_reg <= 2'b11;  // Word access

                    // Address calculation
                    if (mem_transfer_count == 0) begin
                        mem_addr_reg <= mem_addr_reg;  // Use captured EA
                    end else begin
                        mem_addr_reg <= mem_addr_reg + 2;
                    end

                    // Select word to write
                    case (mem_transfer_count)
                        4'h0: mem_data_out_reg <= mem_operand_buffer[15:0];
                        4'h1: mem_data_out_reg <= mem_operand_buffer[31:16];
                        4'h2: mem_data_out_reg <= mem_operand_buffer[47:32];
                        4'h3: mem_data_out_reg <= mem_operand_buffer[63:48];
                        4'h4: mem_data_out_reg <= mem_operand_buffer[79:64];
                    endcase

                    if (mem_ack) begin
                        mem_transfer_count <= mem_transfer_count + 1;

                        if ((current_operand_size == 2'b00 && mem_transfer_count >= 0) ||
                            (current_operand_size == 2'b01 && mem_transfer_count >= 1) ||
                            (current_operand_size == 2'b10 && mem_transfer_count >= 3) ||
                            (current_operand_size == 2'b11 && mem_transfer_count >= 4)) begin
                            mem_state <= MEM_COMPLETE;
                            mem_access_reg <= 1'b0;
                            mem_wr_en_reg <= 1'b0;
                        end
                    end
                end

                MEM_COMPLETE: begin
                    mem_operation_complete <= 1'b1;
                    mem_state <= MEM_IDLE;
                end

                default: mem_state <= MEM_IDLE;
            endcase
        end
    end

    //=================================================================
    // Main Interface State Machine (Queue-Driven)
    //=================================================================

    always @(posedge clk) begin
        if (reset) begin
            state <= STATE_IDLE;
            internal_busy <= 1'b0;
            instruction_ack <= 1'b0;
            queue_enqueue <= 1'b0;
            queue_dequeue <= 1'b0;
            core_execute <= 1'b0;
            operand_buffer <= 80'h0;
            result_buffer <= 80'h0;
            needs_mem_load <= 1'b0;
            needs_mem_store <= 1'b0;
            current_opcode <= 8'h00;
            current_stack_index <= 3'b0;
            current_has_memory_op <= 1'b0;
            current_operand_size <= 2'b0;
            current_is_integer <= 1'b0;
            current_is_bcd <= 1'b0;
            core_data_in <= 80'h0;
            core_int_data_in <= 32'h0;
        end else begin
            // Default: deassert one-shot signals
            instruction_ack <= 1'b0;
            queue_enqueue <= 1'b0;
            queue_dequeue <= 1'b0;
            core_execute <= 1'b0;

            // Enqueue logic: Always try to enqueue when CPU sends instruction
            if (cpu_fpu_instr_valid && decoded_valid && !queue_full) begin
                instruction_ack <= 1'b1;
                queue_enqueue <= 1'b1;
            end

            case (state)
                STATE_IDLE: begin
                    internal_busy <= 1'b0;

                    // Process queued instructions when available and not busy
                    if (!queue_empty && !internal_busy) begin
                        queue_dequeue <= 1'b1;
                        internal_busy <= 1'b1;

                        // Capture from queue (not from CPU!)
                        current_opcode <= queued_opcode;
                        current_stack_index <= queued_stack_index;
                        current_has_memory_op <= queued_has_memory_op;
                        current_operand_size <= queued_operand_size;
                        current_is_integer <= queued_is_integer;
                        current_is_bcd <= queued_is_bcd;

                        // Initialize memory address with EA from queue
                        mem_addr_reg <= queued_ea;

                        // Determine operation type
                        if (queued_has_memory_op) begin
                            // Memory operand instruction
                            needs_mem_load <= 1'b1;
                            needs_mem_store <= queued_has_pop;  // Store operations pop
                            state <= STATE_MEM_LOAD;
                        end else begin
                            // Register-only operation
                            needs_mem_load <= 1'b0;
                            needs_mem_store <= 1'b0;
                            state <= STATE_EXECUTE;
                        end
                    end
                end

                STATE_MEM_LOAD: begin
                    // Wait for memory read to complete
                    if (mem_operation_complete) begin
                        operand_buffer <= mem_operand_buffer;
                        state <= STATE_EXECUTE;
                    end
                end

                STATE_EXECUTE: begin
                    // Execute instruction on FPU core
                    if (core_ready) begin
                        // Prepare data for core
                        if (needs_mem_load) begin
                            core_data_in <= operand_buffer;
                        end else begin
                            core_data_in <= 80'h0;
                        end

                        core_int_data_in <= 32'h0;
                        core_execute <= 1'b1;
                        state <= STATE_RESULT;
                    end
                end

                STATE_RESULT: begin
                    // Wait for core to complete
                    if (!core_busy && core_ready) begin
                        result_buffer <= core_data_out;

                        if (needs_mem_store) begin
                            state <= STATE_MEM_STORE;
                        end else begin
                            internal_busy <= 1'b0;
                            state <= STATE_IDLE;
                        end
                    end
                end

                STATE_MEM_STORE: begin
                    // Wait for memory write to complete
                    if (mem_operation_complete) begin
                        internal_busy <= 1'b0;
                        state <= STATE_IDLE;
                    end
                end

                default: state <= STATE_IDLE;
            endcase
        end
    end

    //=================================================================
    // Output Assignments
    //=================================================================

    // CPU Interface
    assign cpu_fpu_instr_ack = instruction_ack;
    assign cpu_fpu_busy = internal_busy || !queue_empty || core_busy;
    assign cpu_fpu_status_word = core_status_out;
    assign cpu_fpu_exception = core_error;
    assign cpu_fpu_irq = core_int_request;

    // Memory Interface
    assign mem_addr = mem_addr_reg;
    assign mem_data_out = mem_data_out_reg;
    assign mem_access = mem_access_reg;
    assign mem_wr_en = mem_wr_en_reg;
    assign mem_bytesel = mem_bytesel_reg;

endmodule
