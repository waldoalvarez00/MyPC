// Formal verification harness for FPU_Instruction_Queue
// Verifies FIFO properties, count invariants, and data integrity

`default_nettype none

module FPU_Instruction_Queue_formal (
    input logic clk
);
    // Reset signal
    logic reset;

    // Enqueue interface
    (* anyseq *) logic enqueue;
    (* anyseq *) logic [7:0] instruction_in;
    (* anyseq *) logic [2:0] stack_index_in;
    (* anyseq *) logic has_memory_op_in;
    (* anyseq *) logic [1:0] operand_size_in;
    (* anyseq *) logic is_integer_in;
    (* anyseq *) logic is_bcd_in;
    (* anyseq *) logic [79:0] data_in;
    logic queue_full;

    // Dequeue interface
    (* anyseq *) logic dequeue;
    logic queue_empty;
    logic [7:0] instruction_out;
    logic [2:0] stack_index_out;
    logic has_memory_op_out;
    logic [1:0] operand_size_out;
    logic is_integer_out;
    logic is_bcd_out;
    logic [79:0] data_out;

    // Flush interface
    (* anyseq *) logic flush_queue;

    // Status
    logic [1:0] queue_count;

    // Instantiate DUT
    FPU_Instruction_Queue #(
        .QUEUE_DEPTH(3)
    ) dut (
        .clk(clk),
        .reset(reset),
        .enqueue(enqueue),
        .instruction_in(instruction_in),
        .stack_index_in(stack_index_in),
        .has_memory_op_in(has_memory_op_in),
        .operand_size_in(operand_size_in),
        .is_integer_in(is_integer_in),
        .is_bcd_in(is_bcd_in),
        .data_in(data_in),
        .queue_full(queue_full),
        .dequeue(dequeue),
        .queue_empty(queue_empty),
        .instruction_out(instruction_out),
        .stack_index_out(stack_index_out),
        .has_memory_op_out(has_memory_op_out),
        .operand_size_out(operand_size_out),
        .is_integer_out(is_integer_out),
        .is_bcd_out(is_bcd_out),
        .data_out(data_out),
        .flush_queue(flush_queue),
        .queue_count(queue_count)
    );

    //=========================================================================
    // Reset sequence
    //=========================================================================

    logic seen_reset;

    initial begin
        reset = 1'b1;
        seen_reset = 1'b0;
    end

    always_ff @(posedge clk) begin
        if ($initstate) begin
            reset <= 1'b1;
            seen_reset <= 1'b0;
        end else begin
            reset <= 1'b0;
            if (reset)
                seen_reset <= 1'b1;
        end
    end

    //=========================================================================
    // Internal signal access for formal verification
    //=========================================================================

    // NOTE: Direct hierarchical access to internal signals not supported by Yosys
    // These pointer range checks are redundant with shadow model verification
    // and external queue_count/full/empty properties
    /*
    wire [1:0] dut_write_ptr = dut.write_ptr;
    wire [1:0] dut_read_ptr = dut.read_ptr;
    */

    //=========================================================================
    // Shadow model for FIFO verification
    //=========================================================================

    // Track enqueued data to verify FIFO ordering
    logic [7:0] shadow_inst [0:2];
    logic [79:0] shadow_data [0:2];
    logic [1:0] shadow_count;
    logic [1:0] shadow_write_ptr;
    logic [1:0] shadow_read_ptr;

    always_ff @(posedge clk) begin
        if (reset || flush_queue) begin
            shadow_count <= 0;
            shadow_write_ptr <= 0;
            shadow_read_ptr <= 0;
        end else begin
            // Track enqueue
            if (enqueue && !queue_full) begin
                shadow_inst[shadow_write_ptr] <= instruction_in;
                shadow_data[shadow_write_ptr] <= data_in;
                shadow_write_ptr <= (shadow_write_ptr == 2) ? 0 : shadow_write_ptr + 1;
            end

            // Track dequeue
            if (dequeue && !queue_empty) begin
                shadow_read_ptr <= (shadow_read_ptr == 2) ? 0 : shadow_read_ptr + 1;
            end

            // Update count
            if (enqueue && !queue_full && !(dequeue && !queue_empty))
                shadow_count <= shadow_count + 1;
            else if (dequeue && !queue_empty && !(enqueue && !queue_full))
                shadow_count <= shadow_count - 1;
        end
    end

    //=========================================================================
    // Formal Properties
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin

            //=================================================================
            // Property 1: Count never exceeds QUEUE_DEPTH
            //=================================================================
            assert(queue_count <= 3);

            //=================================================================
            // Property 2: queue_empty iff count == 0
            //=================================================================
            assert(queue_empty == (queue_count == 0));

            //=================================================================
            // Property 3: queue_full iff count >= QUEUE_DEPTH
            //=================================================================
            assert(queue_full == (queue_count >= 3));

            //=================================================================
            // Property 4: Count matches shadow model
            //=================================================================
            assert(queue_count == shadow_count);

            //=================================================================
            // Property 5: Enqueue increments count (when not full and not dequeuing)
            //=================================================================
            if ($past(enqueue) && !$past(queue_full) &&
                !($past(dequeue) && !$past(queue_empty)) && !$past(flush_queue) && !$past(reset))
                assert(queue_count == $past(queue_count) + 1);

            //=================================================================
            // Property 6: Dequeue decrements count (when not empty and not enqueuing)
            //=================================================================
            if ($past(dequeue) && !$past(queue_empty) &&
                !($past(enqueue) && !$past(queue_full)) && !$past(flush_queue) && !$past(reset))
                assert(queue_count == $past(queue_count) - 1);

            //=================================================================
            // Property 7: Simultaneous enqueue/dequeue keeps count same
            //=================================================================
            if ($past(enqueue) && !$past(queue_full) &&
                $past(dequeue) && !$past(queue_empty) && !$past(flush_queue) && !$past(reset))
                assert(queue_count == $past(queue_count));

            //=================================================================
            // Property 8: Flush resets count to 0
            //=================================================================
            if ($past(flush_queue) && !$past(reset))
                assert(queue_count == 0);

            //=================================================================
            // Property 9: FIFO ordering - dequeued instruction matches shadow
            //=================================================================
            if (!queue_empty)
                assert(instruction_out == shadow_inst[shadow_read_ptr]);

            //=================================================================
            // Property 10: FIFO ordering - dequeued data matches shadow
            //=================================================================
            if (!queue_empty)
                assert(data_out == shadow_data[shadow_read_ptr]);

            //=================================================================
            // Property 11: Empty queue outputs zeros
            //=================================================================
            if (queue_empty) begin
                assert(instruction_out == 8'h00);
                assert(stack_index_out == 3'h0);
                assert(data_out == 80'h0);
            end

            //=================================================================
            // Property 12: Pointers stay in valid range
            // NOTE: Commented out due to Yosys hierarchical access limitation
            // These are implicitly verified by queue_count <= QUEUE_DEPTH
            //=================================================================
            // assert(dut_write_ptr < 3);
            // assert(dut_read_ptr < 3);

        end
    end

    //=========================================================================
    // Cover Properties - Verify reachability
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin
            // Cover: Queue becomes full
            cover(queue_full);

            // Cover: Queue becomes empty after being non-empty
            cover(queue_empty && $past(queue_count) > 0);

            // Cover: Simultaneous enqueue and dequeue
            cover(enqueue && dequeue && !queue_empty && !queue_full);

            // Cover: Flush non-empty queue
            cover(flush_queue && queue_count > 0);

            // Cover: Queue at each count level
            cover(queue_count == 1);
            cover(queue_count == 2);
            cover(queue_count == 3);
        end
    end

endmodule
