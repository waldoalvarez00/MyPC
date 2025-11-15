// ================================================================
// Unit Test for IP (Instruction Pointer)
// Tests IP increment, rollback, and write operations
// ================================================================

`timescale 1ns/1ps

module ip_tb;

    // DUT signals
    logic clk;
    logic reset;
    logic start_instruction;
    logic next_instruction;
    logic rollback;
    logic [3:0] inc;
    logic wr_en;
    logic [15:0] wr_val;
    logic [15:0] val;

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Instantiate DUT
    IP dut (
        .clk(clk),
        .reset(reset),
        .start_instruction(start_instruction),
        .next_instruction(next_instruction),
        .rollback(rollback),
        .inc(inc),
        .wr_en(wr_en),
        .wr_val(wr_val),
        .val(val)
    );

    // Clock generation: 50 MHz
    initial begin
        clk = 0;
        forever #10 clk = ~clk;
    end

    task check_result(input string test_name, input logic [15:0] expected);
        test_count++;
        if (val == expected) begin
            $display("[PASS] Test %0d: %s (IP=0x%04h)", test_count, test_name, val);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s (expected 0x%04h, got 0x%04h)",
                     test_count, test_name, expected, val);
            fail_count++;
        end
    endtask

    // Main test sequence
    initial begin
        $display("================================================================");
        $display("IP (Instruction Pointer) Unit Test");
        $display("================================================================\n");

        // Initialize
        reset = 1;
        start_instruction = 0;
        next_instruction = 0;
        rollback = 0;
        inc = 0;
        wr_en = 0;
        wr_val = 0;

        repeat(3) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        // ================================================================
        // TEST 1: Reset State
        // ================================================================
        $display("--- Test 1: Reset State ---");

        check_result("IP after reset", 16'h0000);

        // ================================================================
        // TEST 2: Direct Write to IP
        // ================================================================
        $display("\n--- Test 2: Direct Write ---");

        wr_en = 1;
        wr_val = 16'h1234;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("IP after write", 16'h1234);

        // ================================================================
        // TEST 3: Increment IP (start_instruction)
        // ================================================================
        $display("\n--- Test 3: Increment on Start Instruction ---");

        // Set IP to known value
        wr_en = 1;
        wr_val = 16'h0100;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        // Increment by 1
        start_instruction = 1;
        inc = 4'd1;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("IP after inc by 1", 16'h0101);

        // ================================================================
        // TEST 4: Increment IP by Various Amounts
        // ================================================================
        $display("\n--- Test 4: Various Increments ---");

        // Increment by 2
        start_instruction = 1;
        inc = 4'd2;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("IP after inc by 2", 16'h0103);

        // Increment by 5
        start_instruction = 1;
        inc = 4'd5;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("IP after inc by 5", 16'h0108);

        // ================================================================
        // TEST 5: Rollback to Instruction Start
        // ================================================================
        $display("\n--- Test 5: Rollback ---");

        // Set IP and mark instruction start
        wr_en = 1;
        wr_val = 16'h0200;
        @(posedge clk);
        wr_en = 0;

        start_instruction = 1;
        inc = 4'd0;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        // Increment IP several times
        start_instruction = 1;
        inc = 4'd3;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("IP before rollback", 16'h0203);

        // Rollback to instruction start
        rollback = 1;
        @(posedge clk);
        rollback = 0;
        @(posedge clk);

        check_result("IP after rollback", 16'h0200);

        // ================================================================
        // TEST 6: Next Instruction
        // ================================================================
        $display("\n--- Test 6: Next Instruction ---");

        // Set IP
        wr_en = 1;
        wr_val = 16'h0300;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        // Mark as instruction start
        next_instruction = 1;
        @(posedge clk);
        next_instruction = 0;
        @(posedge clk);

        // Increment
        start_instruction = 1;
        inc = 4'd4;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("IP after increment", 16'h0304);

        // Rollback should go to 0x0300
        rollback = 1;
        @(posedge clk);
        rollback = 0;
        @(posedge clk);

        check_result("Rollback to instruction start", 16'h0300);

        // ================================================================
        // TEST 7: Write Overrides Increment
        // ================================================================
        $display("\n--- Test 7: Write vs Increment Priority ---");

        wr_en = 1;
        wr_val = 16'h0500;
        start_instruction = 1;
        inc = 4'd10;
        @(posedge clk);
        wr_en = 0;
        start_instruction = 0;
        @(posedge clk);

        check_result("Write takes priority over increment", 16'h0500);

        // ================================================================
        // TEST 8: Wrap Around (16-bit overflow)
        // ================================================================
        $display("\n--- Test 8: 16-bit Wrap Around ---");

        wr_en = 1;
        wr_val = 16'hFFFE;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        start_instruction = 1;
        inc = 4'd5;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("16-bit wrap around", 16'h0003);

        // ================================================================
        // TEST 9: Multiple Start Instructions
        // ================================================================
        $display("\n--- Test 9: Sequential Increments ---");

        wr_en = 1;
        wr_val = 16'h1000;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        // Series of increments
        for (int i = 0; i < 5; i++) begin
            start_instruction = 1;
            inc = 4'd1;
            @(posedge clk);
            start_instruction = 0;
            @(posedge clk);
        end

        check_result("After 5 increments of 1", 16'h1005);

        // ================================================================
        // TEST 10: Instruction Start Address Tracking
        // ================================================================
        $display("\n--- Test 10: Instruction Start Tracking ---");

        // Write initial value
        wr_en = 1;
        wr_val = 16'h2000;
        next_instruction = 1;
        @(posedge clk);
        wr_en = 0;
        next_instruction = 0;
        @(posedge clk);

        // Increment multiple times
        start_instruction = 1;
        inc = 4'd2;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        start_instruction = 1;
        inc = 4'd3;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("After increments", 16'h2005);

        // Rollback should go to 0x2000
        rollback = 1;
        @(posedge clk);
        rollback = 0;
        @(posedge clk);

        check_result("Rollback to tracked start", 16'h2000);

        // ================================================================
        // TEST 11: Zero Increment
        // ================================================================
        $display("\n--- Test 11: Zero Increment ---");

        wr_en = 1;
        wr_val = 16'h3000;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        start_instruction = 1;
        inc = 4'd0;
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("Zero increment (no change)", 16'h3000);

        // ================================================================
        // TEST 12: Maximum Increment
        // ================================================================
        $display("\n--- Test 12: Maximum Increment ---");

        wr_en = 1;
        wr_val = 16'h4000;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        start_instruction = 1;
        inc = 4'd15;  // Maximum 4-bit value
        @(posedge clk);
        start_instruction = 0;
        @(posedge clk);

        check_result("Maximum increment (15)", 16'h400F);

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
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓\n");
            $finish(0);
        end else begin
            $display("✗✗✗ SOME TESTS FAILED ✗✗✗\n");
            $finish(1);
        end
    end

endmodule
