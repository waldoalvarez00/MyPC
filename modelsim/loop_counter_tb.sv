// ================================================================
// Unit Test for LoopCounter
// Tests microcode loop counter functionality
// ================================================================

`timescale 1ns/1ps

module loop_counter_tb;

    // DUT signals
    logic clk;
    logic [4:0] count_in;
    logic load;
    logic next;
    logic done;

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Instantiate DUT
    LoopCounter dut (
        .clk(clk),
        .count_in(count_in),
        .load(load),
        .next(next),
        .done(done)
    );

    // Clock generation: 50 MHz
    initial begin
        clk = 0;
        forever #10 clk = ~clk;
    end

    // Helper task to load a value
    task do_load(input [4:0] val);
        #1;
        count_in = val;
        load = 1;
        #1;
        @(posedge clk);
        #1;
        load = 0;
        #1;
        @(posedge clk);
        #1;
    endtask

    // Helper task to decrement
    task do_next();
        #1;
        next = 1;
        #1;
        @(posedge clk);
        #1;
        next = 0;
        #1;
    endtask

    // Helper task to decrement N times
    task do_next_n(input int n);
        #1;
        next = 1;
        #1;
        repeat(n) @(posedge clk);
        #1;
        next = 0;
        #1;
        @(posedge clk);
        #1;
    endtask

    task check_done(input string test_name, input logic expected);
        #5;  // Let combinational logic settle
        test_count++;
        if (done === expected) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s (done=%b, count=%d)", test_count, test_name, done, dut.count);
            fail_count++;
        end
    endtask

    // Main test sequence
    initial begin
        $display("================================================================");
        $display("LoopCounter Unit Test");
        $display("================================================================\n");

        // Initialize
        count_in = 0;
        load = 0;
        next = 0;

        repeat(3) @(posedge clk);
        #1;

        // ================================================================
        // TEST 1: Initial State (done should be true for count=0)
        // ================================================================
        $display("--- Test 1: Initial State ---");

        check_done("Done true when count=0", 1);

        // ================================================================
        // TEST 2: Load Count
        // ================================================================
        $display("\n--- Test 2: Load Count ---");

        do_load(5'd5);
        check_done("Done false after loading 5", 0);

        // ================================================================
        // TEST 3: Decrement Counter
        // ================================================================
        $display("\n--- Test 3: Decrement ---");

        do_next();
        check_done("After 1st decrement, done=0", 0);

        do_next();
        check_done("After 2nd decrement, done=0", 0);

        do_next();
        check_done("After 3rd decrement, done=0", 0);

        do_next();
        check_done("After 4th decrement, done=0", 0);

        do_next();
        check_done("After 5th decrement, done=1", 1);

        // ================================================================
        // TEST 4: Load While Counting
        // ================================================================
        $display("\n--- Test 4: Reload During Count ---");

        do_load(5'd3);
        do_next();

        // Reload with new value
        do_load(5'd10);
        check_done("Reloaded count, done=0", 0);

        // ================================================================
        // TEST 5: Count Down to Zero
        // ================================================================
        $display("\n--- Test 5: Full Countdown ---");

        do_load(5'd3);
        do_next_n(3);
        check_done("Full countdown complete", 1);

        // ================================================================
        // TEST 6: Load Zero
        // ================================================================
        $display("\n--- Test 6: Load Zero ---");

        do_load(5'd0);
        check_done("Loaded zero, done=1", 1);

        // ================================================================
        // TEST 7: Load Maximum Value
        // ================================================================
        $display("\n--- Test 7: Load Maximum ---");

        do_load(5'd31);
        check_done("Loaded max value, done=0", 0);

        // Decrement a few times
        do_next_n(5);
        check_done("After partial countdown, done=0", 0);

        // ================================================================
        // TEST 8: Next Without Load (at zero)
        // ================================================================
        $display("\n--- Test 8: Next Without Load ---");

        do_load(5'd0);
        do_next();
        do_next();
        check_done("Next at zero doesn't underflow", 1);

        // ================================================================
        // TEST 9: Rapid Load/Next
        // ================================================================
        $display("\n--- Test 9: Rapid Operations ---");

        #1;
        count_in = 5'd2;
        load = 1;
        next = 1;
        #1;
        @(posedge clk);
        #1;
        load = 0;
        @(posedge clk);
        @(posedge clk);
        #1;
        next = 0;
        #1;
        @(posedge clk);
        #1;

        check_done("Rapid load/next operations", 1);

        // ================================================================
        // TEST 10: Single Count
        // ================================================================
        $display("\n--- Test 10: Single Count ---");

        do_load(5'd1);
        check_done("Loaded 1, done=0", 0);

        do_next();
        check_done("After single decrement, done=1", 1);

        // ================================================================
        // Summary
        // ================================================================
        $display("\n================================================================");
        $display("TEST SUMMARY");
        $display("================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %0d%%", (pass_count * 100) / test_count);
        $display("================================================================");

        if (fail_count == 0) begin
            $display("*** ALL TESTS PASSED ***\n");
            $finish(0);
        end else begin
            $display("*** SOME TESTS FAILED ***\n");
            $finish(1);
        end
    end

endmodule
