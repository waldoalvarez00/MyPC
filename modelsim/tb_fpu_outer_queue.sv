/**
 * tb_fpu_outer_queue.sv
 *
 * Testbench for FPU_Outer_Queue module
 *
 * Tests:
 * 1. Basic enqueue/dequeue
 * 2. Full queue behavior (4-entry depth)
 * 3. Empty queue behavior
 * 4. Wraparound
 * 5. Simultaneous enqueue/dequeue
 * 6. All fields properly stored and retrieved
 *
 * Date: 2025-11-20
 */

`timescale 1ns/1ps

module tb_fpu_outer_queue;

    //=================================================================
    // Testbench Signals
    //=================================================================

    reg clk;
    reg reset;

    // Enqueue interface
    reg        enqueue;
    reg [7:0]  opcode_in;
    reg [2:0]  stack_index_in;
    reg [19:0] ea_in;
    reg [1:0]  operand_size_in;
    reg        is_integer_in;
    reg        is_bcd_in;
    reg        has_memory_op_in;
    reg        has_pop_in;
    wire       queue_full;

    // Dequeue interface
    reg        dequeue;
    wire [7:0] opcode_out;
    wire [2:0] stack_index_out;
    wire [19:0] ea_out;
    wire [1:0]  operand_size_out;
    wire        is_integer_out;
    wire        is_bcd_out;
    wire        has_memory_op_out;
    wire        has_pop_out;
    wire        queue_empty;

    // Status
    wire [2:0]  queue_count;

    //=================================================================
    // Test Statistics
    //=================================================================

    integer test_count;
    integer pass_count;
    integer fail_count;

    //=================================================================
    // DUT Instantiation
    //=================================================================

    FPU_Outer_Queue dut (
        .clk(clk),
        .reset(reset),
        .enqueue(enqueue),
        .opcode_in(opcode_in),
        .stack_index_in(stack_index_in),
        .ea_in(ea_in),
        .operand_size_in(operand_size_in),
        .is_integer_in(is_integer_in),
        .is_bcd_in(is_bcd_in),
        .has_memory_op_in(has_memory_op_in),
        .has_pop_in(has_pop_in),
        .queue_full(queue_full),
        .dequeue(dequeue),
        .opcode_out(opcode_out),
        .stack_index_out(stack_index_out),
        .ea_out(ea_out),
        .operand_size_out(operand_size_out),
        .is_integer_out(is_integer_out),
        .is_bcd_out(is_bcd_out),
        .has_memory_op_out(has_memory_op_out),
        .has_pop_out(has_pop_out),
        .queue_empty(queue_empty),
        .queue_count(queue_count)
    );

    //=================================================================
    // Clock Generation
    //=================================================================

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    //=================================================================
    // Test Tasks
    //=================================================================

    // Task: Enqueue an instruction with all fields
    task enqueue_instruction;
        input [7:0]  opcode;
        input [2:0]  idx;
        input [19:0] ea;
        input [1:0]  size;
        input        is_int;
        input        is_bcd_val;
        input        has_mem;
        input        has_pop_val;
        begin
            @(posedge clk);
            enqueue <= 1'b1;
            opcode_in <= opcode;
            stack_index_in <= idx;
            ea_in <= ea;
            operand_size_in <= size;
            is_integer_in <= is_int;
            is_bcd_in <= is_bcd_val;
            has_memory_op_in <= has_mem;
            has_pop_in <= has_pop_val;
            @(posedge clk);
            enqueue <= 1'b0;
        end
    endtask

    // Task: Dequeue an instruction
    task dequeue_instruction;
        begin
            @(posedge clk);
            dequeue <= 1'b1;
            @(posedge clk);
            dequeue <= 1'b0;
        end
    endtask

    // Task: Check queue status
    task check_status;
        input [2:0] expected_count;
        input expected_empty;
        input expected_full;
        input [255:0] test_name;
        begin
            test_count = test_count + 1;
            $display("[Test %0d] %s", test_count, test_name);

            if (queue_count == expected_count &&
                queue_empty == expected_empty &&
                queue_full == expected_full) begin
                $display("  PASS: count=%d, empty=%b, full=%b",
                         queue_count, queue_empty, queue_full);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: Expected count=%d empty=%b full=%b, Got count=%d empty=%b full=%b",
                         expected_count, expected_empty, expected_full,
                         queue_count, queue_empty, queue_full);
                fail_count = fail_count + 1;
            end
        end
    endtask

    // Task: Check dequeued instruction (all fields)
    task check_instruction;
        input [7:0]  expected_opcode;
        input [2:0]  expected_idx;
        input [19:0] expected_ea;
        input [1:0]  expected_size;
        input        expected_int;
        input        expected_bcd;
        input        expected_mem;
        input        expected_pop;
        input [255:0] test_name;
        begin
            test_count = test_count + 1;
            $display("[Test %0d] %s", test_count, test_name);

            if (opcode_out == expected_opcode &&
                stack_index_out == expected_idx &&
                ea_out == expected_ea &&
                operand_size_out == expected_size &&
                is_integer_out == expected_int &&
                is_bcd_out == expected_bcd &&
                has_memory_op_out == expected_mem &&
                has_pop_out == expected_pop) begin
                $display("  PASS: opcode=0x%02h, idx=%d, ea=0x%05h, size=%d, int=%b, bcd=%b, mem=%b, pop=%b",
                         opcode_out, stack_index_out, ea_out, operand_size_out,
                         is_integer_out, is_bcd_out, has_memory_op_out, has_pop_out);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: Expected opcode=0x%02h idx=%d ea=0x%05h size=%d int=%b bcd=%b mem=%b pop=%b",
                         expected_opcode, expected_idx, expected_ea, expected_size,
                         expected_int, expected_bcd, expected_mem, expected_pop);
                $display("        Got opcode=0x%02h idx=%d ea=0x%05h size=%d int=%b bcd=%b mem=%b pop=%b",
                         opcode_out, stack_index_out, ea_out, operand_size_out,
                         is_integer_out, is_bcd_out, has_memory_op_out, has_pop_out);
                fail_count = fail_count + 1;
            end
        end
    endtask

    //=================================================================
    // Main Test Sequence
    //=================================================================

    initial begin
        // Initialize
        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        enqueue = 0;
        opcode_in = 0;
        stack_index_in = 0;
        ea_in = 0;
        operand_size_in = 0;
        is_integer_in = 0;
        is_bcd_in = 0;
        has_memory_op_in = 0;
        has_pop_in = 0;
        dequeue = 0;

        // Reset
        reset = 1;
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        $display("\n=== FPU Outer Queue Tests ===\n");

        // Test 1: Initial state (empty)
        check_status(3'd0, 1'b1, 1'b0, "Initial state - empty queue");

        // Test 2: Enqueue first instruction (FADD with memory)
        enqueue_instruction(8'hD8, 3'd0, 20'h12345, 2'd1, 1'b0, 1'b0, 1'b1, 1'b0);
        @(posedge clk);
        check_status(3'd1, 1'b0, 1'b0, "After enqueue 1 - count=1");

        // Test 3: Verify first instruction
        check_instruction(8'hD8, 3'd0, 20'h12345, 2'd1, 1'b0, 1'b0, 1'b1, 1'b0,
                         "Verify first instruction (FADD)");

        // Test 4: Enqueue second instruction (FILD integer)
        enqueue_instruction(8'hDA, 3'd1, 20'hABCDE, 2'd1, 1'b1, 1'b0, 1'b1, 1'b0);
        @(posedge clk);
        check_status(3'd2, 1'b0, 1'b0, "After enqueue 2 - count=2");

        // Test 5: Enqueue third instruction (FBLD BCD)
        enqueue_instruction(8'hDF, 3'd2, 20'h55555, 2'd3, 1'b0, 1'b1, 1'b1, 1'b0);
        @(posedge clk);
        check_status(3'd3, 1'b0, 1'b0, "After enqueue 3 - count=3");

        // Test 6: Enqueue fourth instruction (FSTP with pop)
        enqueue_instruction(8'hDD, 3'd0, 20'hFFFFF, 2'd2, 1'b0, 1'b0, 1'b1, 1'b1);
        @(posedge clk);
        check_status(3'd4, 1'b0, 1'b1, "After enqueue 4 - queue full");

        // Test 7: Try to enqueue to full queue (should fail)
        enqueue_instruction(8'hFF, 3'd7, 20'h00000, 2'd0, 1'b0, 1'b0, 1'b0, 1'b0);
        @(posedge clk);
        check_status(3'd4, 1'b0, 1'b1, "Enqueue to full - still full");

        // Test 8: Dequeue first instruction
        dequeue_instruction();
        @(posedge clk);
        check_status(3'd3, 1'b0, 1'b0, "After dequeue 1 - count=3");

        // Test 9: Verify second instruction (now at head)
        check_instruction(8'hDA, 3'd1, 20'hABCDE, 2'd1, 1'b1, 1'b0, 1'b1, 1'b0,
                         "Verify second instruction (FILD)");

        // Test 10: Dequeue second
        dequeue_instruction();
        @(posedge clk);
        check_status(3'd2, 1'b0, 1'b0, "After dequeue 2 - count=2");

        // Test 11: Verify third instruction (BCD)
        check_instruction(8'hDF, 3'd2, 20'h55555, 2'd3, 1'b0, 1'b1, 1'b1, 1'b0,
                         "Verify third instruction (FBLD BCD)");

        // Test 12: Dequeue third
        dequeue_instruction();
        @(posedge clk);
        check_status(3'd1, 1'b0, 1'b0, "After dequeue 3 - count=1");

        // Test 13: Verify fourth instruction (with pop)
        check_instruction(8'hDD, 3'd0, 20'hFFFFF, 2'd2, 1'b0, 1'b0, 1'b1, 1'b1,
                         "Verify fourth instruction (FSTP pop)");

        // Test 14: Enqueue while one entry present (wraparound test)
        enqueue_instruction(8'hD9, 3'd5, 20'h77777, 2'd0, 1'b0, 1'b0, 1'b0, 1'b0);
        @(posedge clk);
        check_status(3'd2, 1'b0, 1'b0, "Wraparound enqueue - count=2");

        // Test 15: Dequeue to verify wraparound
        dequeue_instruction();
        @(posedge clk);
        check_status(3'd1, 1'b0, 1'b0, "After wraparound dequeue - count=1");

        // Test 16: Verify wraparound entry
        check_instruction(8'hD9, 3'd5, 20'h77777, 2'd0, 1'b0, 1'b0, 1'b0, 1'b0,
                         "Verify wraparound instruction");

        // Test 17: Simultaneous enqueue and dequeue
        @(posedge clk);
        enqueue <= 1'b1;
        dequeue <= 1'b1;
        opcode_in <= 8'hDC;
        stack_index_in <= 3'd3;
        ea_in <= 20'h99999;
        operand_size_in <= 2'd2;
        is_integer_in <= 1'b0;
        is_bcd_in <= 1'b0;
        has_memory_op_in <= 1'b1;
        has_pop_in <= 1'b0;
        @(posedge clk);
        enqueue <= 1'b0;
        dequeue <= 1'b0;
        @(posedge clk);
        check_status(3'd1, 1'b0, 1'b0, "Simultaneous enq/deq - count unchanged");

        // Test 18: Verify simultaneous operation result
        check_instruction(8'hDC, 3'd3, 20'h99999, 2'd2, 1'b0, 1'b0, 1'b1, 1'b0,
                         "Verify simultaneous enq/deq result");

        // Test 19: Dequeue to empty
        dequeue_instruction();
        @(posedge clk);
        check_status(3'd0, 1'b1, 1'b0, "Dequeue to empty");

        // Test 20: Try dequeue from empty (should not crash)
        dequeue_instruction();
        @(posedge clk);
        check_status(3'd0, 1'b1, 1'b0, "Dequeue from empty - still empty");

        // Summary
        repeat(5) @(posedge clk);
        $display("\n=== Test Summary ===");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);

        if (fail_count == 0) begin
            $display("\n*** ALL TESTS PASSED ***\n");
        end else begin
            $display("\n*** SOME TESTS FAILED ***\n");
        end

        $finish;
    end

    //=================================================================
    // Timeout
    //=================================================================

    initial begin
        #100000;  // 100 us timeout
        $display("\n*** TEST TIMEOUT ***\n");
        $finish;
    end

endmodule
