// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// FPU Outer Instruction Queue
//
// Buffers incoming FPU instructions with their effective addresses
// to enable asynchronous/concurrent CPU-FPU operation.
//
// This queue allows the CPU to continue executing while the FPU
// processes memory operands sequentially. Matches authentic 8087
// behavior with 4-entry instruction queue.
//
// Queue entries store:
// - Decoded opcode and format information
// - Effective address (for memory operands)
// - Stack index (for register operands)
//
// Date: 2025-11-13
//=====================================================================

module FPU_Outer_Queue(
    input wire clk,
    input wire reset,

    // ========== Enqueue Interface (from CPU) ==========
    input wire        enqueue,
    input wire [7:0]  opcode_in,
    input wire [2:0]  stack_index_in,
    input wire [19:0] ea_in,              // Effective address
    input wire [1:0]  operand_size_in,    // 0=16bit, 1=32bit, 2=64bit, 3=80bit
    input wire        is_integer_in,
    input wire        is_bcd_in,
    input wire        has_memory_op_in,
    input wire        has_pop_in,
    output wire       queue_full,

    // ========== Dequeue Interface (to FPU execution) ==========
    input wire        dequeue,
    output wire [7:0] opcode_out,
    output wire [2:0] stack_index_out,
    output wire [19:0] ea_out,
    output wire [1:0]  operand_size_out,
    output wire        is_integer_out,
    output wire        is_bcd_out,
    output wire        has_memory_op_out,
    output wire        has_pop_out,
    output wire        queue_empty,

    // ========== Status ==========
    output wire [2:0]  queue_count
);

    //=================================================================
    // Queue Storage (4 entries - authentic 8087 queue depth)
    //=================================================================

    reg [7:0]  queue_opcode [0:3];
    reg [2:0]  queue_stack_index [0:3];
    reg [19:0] queue_ea [0:3];
    reg [1:0]  queue_operand_size [0:3];
    reg        queue_is_integer [0:3];
    reg        queue_is_bcd [0:3];
    reg        queue_has_memory_op [0:3];
    reg        queue_has_pop [0:3];

    //=================================================================
    // Queue Control
    //=================================================================

    reg [1:0] wr_ptr;  // Write pointer (0-3)
    reg [1:0] rd_ptr;  // Read pointer (0-3)
    reg [2:0] count;   // Number of entries (0-4)

    assign queue_full = (count == 3'd4);
    assign queue_empty = (count == 3'd0);
    assign queue_count = count;

    //=================================================================
    // Output Head of Queue
    //=================================================================

    assign opcode_out = queue_opcode[rd_ptr];
    assign stack_index_out = queue_stack_index[rd_ptr];
    assign ea_out = queue_ea[rd_ptr];
    assign operand_size_out = queue_operand_size[rd_ptr];
    assign is_integer_out = queue_is_integer[rd_ptr];
    assign is_bcd_out = queue_is_bcd[rd_ptr];
    assign has_memory_op_out = queue_has_memory_op[rd_ptr];
    assign has_pop_out = queue_has_pop[rd_ptr];

    //=================================================================
    // Queue State Machine
    //=================================================================

    always @(posedge clk) begin
        if (reset) begin
            wr_ptr <= 2'b00;
            rd_ptr <= 2'b00;
            count <= 3'd0;
        end else begin
            // Handle enqueue and dequeue operations
            case ({enqueue && !queue_full, dequeue && !queue_empty})
                2'b10: begin
                    // Enqueue only
                    queue_opcode[wr_ptr] <= opcode_in;
                    queue_stack_index[wr_ptr] <= stack_index_in;
                    queue_ea[wr_ptr] <= ea_in;
                    queue_operand_size[wr_ptr] <= operand_size_in;
                    queue_is_integer[wr_ptr] <= is_integer_in;
                    queue_is_bcd[wr_ptr] <= is_bcd_in;
                    queue_has_memory_op[wr_ptr] <= has_memory_op_in;
                    queue_has_pop[wr_ptr] <= has_pop_in;
                    wr_ptr <= wr_ptr + 2'b01;
                    count <= count + 3'd1;
                end

                2'b01: begin
                    // Dequeue only
                    rd_ptr <= rd_ptr + 2'b01;
                    count <= count - 3'd1;
                end

                2'b11: begin
                    // Simultaneous enqueue and dequeue (queue size unchanged)
                    queue_opcode[wr_ptr] <= opcode_in;
                    queue_stack_index[wr_ptr] <= stack_index_in;
                    queue_ea[wr_ptr] <= ea_in;
                    queue_operand_size[wr_ptr] <= operand_size_in;
                    queue_is_integer[wr_ptr] <= is_integer_in;
                    queue_is_bcd[wr_ptr] <= is_bcd_in;
                    queue_has_memory_op[wr_ptr] <= has_memory_op_in;
                    queue_has_pop[wr_ptr] <= has_pop_in;
                    wr_ptr <= wr_ptr + 2'b01;
                    rd_ptr <= rd_ptr + 2'b01;
                    // count stays same
                end

                // 2'b00: No operation
            endcase
        end
    end

endmodule
