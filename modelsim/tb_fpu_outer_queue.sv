// Copyright 2025, Waldo Alvarez
// Testbench for FPU Outer Queue
// Tests instruction+EA buffering for memory operand support

`timescale 1ns/1ps

module tb_fpu_outer_queue();

    // Clock and reset
    logic clk;
    logic reset;

    // Enqueue interface
    logic        enqueue;
    logic [7:0]  opcode_in;
    logic [2:0]  stack_index_in;
    logic [19:0] ea_in;
    logic [1:0]  operand_size_in;
    logic        is_integer_in;
    logic        is_bcd_in;
    logic        has_memory_op_in;
    logic        has_pop_in;
    logic        queue_full;

    // Dequeue interface
    logic        dequeue;
    logic [7:0]  opcode_out;
    logic [2:0]  stack_index_out;
    logic [19:0] ea_out;
    logic [1:0]  operand_size_out;
    logic        is_integer_out;
    logic        is_bcd_out;
    logic        has_memory_op_out;
    logic        has_pop_out;
    logic        queue_empty;

    // Status
    logic [2:0]  queue_count;

    // Test control
    integer test_passed;
    integer test_failed;

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    // DUT - FPU Outer Queue
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

    // Test stimulus
    initial begin
        $display("=========================================");
        $display("FPU Outer Queue Test");
        $display("=========================================");

        test_passed = 0;
        test_failed = 0;

        // Initialize signals
        reset = 1;
        enqueue = 0;
        dequeue = 0;
        opcode_in = 0;
        stack_index_in = 0;
        ea_in = 0;
        operand_size_in = 0;
        is_integer_in = 0;
        is_bcd_in = 0;
        has_memory_op_in = 0;
        has_pop_in = 0;

        // Reset
        repeat(5) @(posedge clk);
        reset = 0;
        @(posedge clk);

        // Test 1: Empty queue state
        $display("\nTest 1: Empty queue state");
        if (queue_empty && !queue_full && queue_count == 0) begin
            $display("  PASS: Queue correctly reports empty state");
            test_passed++;
        end else begin
            $display("  FAIL: Queue state incorrect (empty=%b full=%b count=%d)",
                     queue_empty, queue_full, queue_count);
            test_failed++;
        end

        // Test 2: Enqueue single entry (FLD [BX+SI] - memory operand)
        $display("\nTest 2: Enqueue FLD [mem] instruction");
        @(posedge clk);
        #1;  // Small delay after clock to avoid race
        enqueue = 1;
        opcode_in = 8'hD9;      // FLD opcode
        stack_index_in = 3'h0;  // ST(0)
        ea_in = 20'h12345;      // Effective address from CPU
        operand_size_in = 2'b01; // 32-bit float
        is_integer_in = 0;
        is_bcd_in = 0;
        has_memory_op_in = 1;
        has_pop_in = 0;
        @(posedge clk);  // Clock edge processes enqueue
        #1;
        enqueue = 0;
        @(posedge clk);  // Wait for outputs to settle

        if (!queue_empty && queue_count == 1) begin
            $display("  PASS: Entry enqueued (count=%d)", queue_count);
            test_passed++;
        end else begin
            $display("  FAIL: Queue count incorrect (count=%d)", queue_count);
            test_failed++;
        end

        // Verify output matches input
        if (opcode_out == 8'hD9 && ea_out == 20'h12345 &&
            has_memory_op_out && operand_size_out == 2'b01) begin
            $display("  PASS: Queue outputs correct data");
            test_passed++;
        end else begin
            $display("  FAIL: Queue output mismatch (opcode=%02h ea=%05h)",
                     opcode_out, ea_out);
            test_failed++;
        end

        // Test 3: Enqueue multiple entries
        $display("\nTest 3: Enqueue multiple entries");

        // Entry 2: FADD [mem]
        @(posedge clk);
        #1;
        enqueue = 1;
        opcode_in = 8'hD8;
        ea_in = 20'h54321;
        operand_size_in = 2'b10; // 64-bit double
        has_memory_op_in = 1;
        @(posedge clk);
        #1;
        enqueue = 0;

        // Entry 3: FIST [mem]
        @(posedge clk);
        #1;
        enqueue = 1;
        opcode_in = 8'hDF;
        ea_in = 20'hABCDE;
        operand_size_in = 2'b00; // 16-bit integer
        is_integer_in = 1;
        has_memory_op_in = 1;
        @(posedge clk);
        #1;
        enqueue = 0;
        is_integer_in = 0;

        // Entry 4: FADD ST(0), ST(1) (register only)
        @(posedge clk);
        #1;
        enqueue = 1;
        opcode_in = 8'hD8;
        stack_index_in = 3'h1;
        ea_in = 20'h00000;
        has_memory_op_in = 0; // No memory operand
        @(posedge clk);
        #1;
        enqueue = 0;

        @(posedge clk);
        if (queue_count == 4 && queue_full) begin
            $display("  PASS: Queue full with 4 entries");
            test_passed++;
        end else begin
            $display("  FAIL: Queue count incorrect (count=%d full=%b)",
                     queue_count, queue_full);
            test_failed++;
        end

        // Test 4: Attempt to enqueue when full
        $display("\nTest 4: Enqueue when full (should be ignored)");
        @(posedge clk);
        #1;
        enqueue = 1;
        opcode_in = 8'hFF; // This should be ignored
        @(posedge clk);
        #1;
        enqueue = 0;
        @(posedge clk);

        if (queue_count == 4) begin
            $display("  PASS: Full queue correctly rejects enqueue");
            test_passed++;
        end else begin
            $display("  FAIL: Queue count changed (count=%d)", queue_count);
            test_failed++;
        end

        // Test 5: Dequeue entries in FIFO order
        $display("\nTest 5: Dequeue in FIFO order");

        // Queue has: [FLD D9/12345], [FADD D8/54321], [FIST DF/ABCDE], [FADD D8/00000]
        // Dequeue entry 1 (FLD [mem] - EA=0x12345)
        @(posedge clk);
        #1;
        dequeue = 1;
        @(posedge clk);
        #1;
        dequeue = 0;
        @(posedge clk);

        // After first dequeue, head should be entry 2 (FADD D8/54321)
        if (queue_count == 3 && opcode_out == 8'hD8 && ea_out == 20'h54321) begin
            $display("  PASS: First dequeue correct (EA=%05h count=%d)",
                     ea_out, queue_count);
            test_passed++;
        end else begin
            $display("  FAIL: First dequeue incorrect (opcode=%02h EA=%05h count=%d)",
                     opcode_out, ea_out, queue_count);
            test_failed++;
        end

        // Dequeue entry 2 (FADD [mem] - EA=0x54321)
        // After this, entry 3 should be at head (FIST [mem] - EA=0xABCDE)
        @(posedge clk);
        #1;
        dequeue = 1;
        @(posedge clk);
        #1;
        dequeue = 0;
        @(posedge clk);

        if (queue_count == 2 && opcode_out == 8'hDF && ea_out == 20'hABCDE &&
            is_integer_out) begin
            $display("  PASS: Second dequeue correct (EA=%05h integer=%b)",
                     ea_out, is_integer_out);
            test_passed++;
        end else begin
            $display("  FAIL: Second dequeue incorrect (opcode=%02h EA=%05h count=%d)",
                     opcode_out, ea_out, queue_count);
            test_failed++;
        end

        // Test 6: Simultaneous enqueue and dequeue
        $display("\nTest 6: Simultaneous enqueue and dequeue");
        @(posedge clk);
        #1;
        enqueue = 1;
        dequeue = 1;
        opcode_in = 8'hDA;
        ea_in = 20'h99999;
        has_memory_op_in = 1;
        @(posedge clk);
        #1;
        enqueue = 0;
        dequeue = 0;
        has_memory_op_in = 0;
        @(posedge clk);

        if (queue_count == 2) begin
            $display("  PASS: Simultaneous enq/deq maintains count");
            test_passed++;
        end else begin
            $display("  FAIL: Count incorrect after simultaneous ops (count=%d)",
                     queue_count);
            test_failed++;
        end

        // Test 7: Drain queue to empty
        $display("\nTest 7: Drain queue to empty");
        while (!queue_empty) begin
            @(posedge clk);
            #1;
            dequeue = 1;
            @(posedge clk);
            #1;
            dequeue = 0;
            @(posedge clk);
        end

        if (queue_empty && queue_count == 0) begin
            $display("  PASS: Queue drained to empty");
            test_passed++;
        end else begin
            $display("  FAIL: Queue not empty (count=%d)", queue_count);
            test_failed++;
        end

        // Test 8: Dequeue from empty queue (should be ignored)
        $display("\nTest 8: Dequeue from empty queue");
        @(posedge clk);
        #1;
        dequeue = 1;
        @(posedge clk);
        #1;
        dequeue = 0;
        @(posedge clk);

        if (queue_empty && queue_count == 0) begin
            $display("  PASS: Empty queue correctly ignores dequeue");
            test_passed++;
        end else begin
            $display("  FAIL: Queue state changed (count=%d)", queue_count);
            test_failed++;
        end

        // Test 9: Queue wrapping (test circular buffer behavior)
        $display("\nTest 9: Queue pointer wrapping");

        // Fill queue
        for (int i = 0; i < 4; i++) begin
            @(posedge clk);
            #1;
            enqueue = 1;
            opcode_in = 8'h10 + i;
            ea_in = 20'h10000 + i;
            @(posedge clk);
            #1;
            enqueue = 0;
            @(posedge clk);
        end

        // Partially drain
        for (int i = 0; i < 3; i++) begin
            @(posedge clk);
            #1;
            dequeue = 1;
            @(posedge clk);
            #1;
            dequeue = 0;
            @(posedge clk);
        end

        // Re-fill (tests wrap-around)
        for (int i = 0; i < 3; i++) begin
            @(posedge clk);
            #1;
            enqueue = 1;
            opcode_in = 8'h20 + i;
            ea_in = 20'h20000 + i;
            @(posedge clk);
            #1;
            enqueue = 0;
            @(posedge clk);
        end

        if (queue_full && queue_count == 4) begin
            $display("  PASS: Queue wrapping works correctly");
            test_passed++;
        end else begin
            $display("  FAIL: Queue wrapping failed (count=%d)", queue_count);
            test_failed++;
        end

        // Summary
        repeat(5) @(posedge clk);
        $display("\n=========================================");
        $display("Test Summary:");
        $display("  Passed: %0d", test_passed);
        $display("  Failed: %0d", test_failed);
        $display("=========================================");

        if (test_failed == 0) begin
            $display("ALL TESTS PASSED!");
            $finish(0);
        end else begin
            $display("SOME TESTS FAILED!");
            $finish(1);
        end
    end

    // Timeout watchdog
    initial begin
        #100000;
        $display("\nERROR: Test timeout!");
        $finish(1);
    end

endmodule
