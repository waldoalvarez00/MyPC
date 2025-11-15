// ================================================================
// Unit Test for TempReg
// Tests temporary register storage
// ================================================================

`timescale 1ns/1ps

module temp_reg_tb;

    // DUT signals
    logic clk;
    logic reset;
    logic [15:0] wr_val;
    logic wr_en;
    logic [15:0] val;

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Instantiate DUT
    TempReg dut (
        .clk(clk),
        .reset(reset),
        .wr_val(wr_val),
        .wr_en(wr_en),
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
            $display("[PASS] Test %0d: %s (val=0x%04h)", test_count, test_name, val);
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
        $display("TempReg Unit Test");
        $display("================================================================\n");

        // Initialize
        reset = 1;
        wr_val = 0;
        wr_en = 0;

        repeat(3) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        // ================================================================
        // TEST 1: Reset State
        // ================================================================
        $display("--- Test 1: Reset State ---");

        check_result("Value after reset", 16'h0000);

        // ================================================================
        // TEST 2: Write Value
        // ================================================================
        $display("\n--- Test 2: Write Value ---");

        wr_val = 16'h1234;
        wr_en = 1;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("After write 0x1234", 16'h1234);

        // ================================================================
        // TEST 3: Write Another Value
        // ================================================================
        $display("\n--- Test 3: Overwrite ---");

        wr_val = 16'h5678;
        wr_en = 1;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("After write 0x5678", 16'h5678);

        // ================================================================
        // TEST 4: Write Without Enable
        // ================================================================
        $display("\n--- Test 4: Write Without Enable ---");

        wr_val = 16'hFFFF;
        wr_en = 0;  // Write disabled
        @(posedge clk);
        @(posedge clk);

        check_result("Value unchanged without wr_en", 16'h5678);

        // ================================================================
        // TEST 5: Multiple Writes
        // ================================================================
        $display("\n--- Test 5: Sequential Writes ---");

        wr_en = 1;
        for (int i = 0; i < 5; i++) begin
            wr_val = 16'h1000 + i;
            @(posedge clk);
        end
        wr_en = 0;
        @(posedge clk);

        check_result("Last value written", 16'h1004);

        // ================================================================
        // TEST 6: Write All Zeros
        // ================================================================
        $display("\n--- Test 6: Write Zeros ---");

        wr_val = 16'h0000;
        wr_en = 1;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("Write all zeros", 16'h0000);

        // ================================================================
        // TEST 7: Write All Ones
        // ================================================================
        $display("\n--- Test 7: Write All Ones ---");

        wr_val = 16'hFFFF;
        wr_en = 1;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("Write all ones", 16'hFFFF);

        // ================================================================
        // TEST 8: Reset During Operation
        // ================================================================
        $display("\n--- Test 8: Reset During Operation ---");

        wr_val = 16'hABCD;
        wr_en = 1;
        @(posedge clk);

        reset = 1;
        @(posedge clk);
        reset = 0;
        wr_en = 0;
        @(posedge clk);

        check_result("Value reset to zero", 16'h0000);

        // ================================================================
        // TEST 9: Value Retention
        // ================================================================
        $display("\n--- Test 9: Value Retention ---");

        wr_val = 16'h9876;
        wr_en = 1;
        @(posedge clk);
        wr_en = 0;

        // Wait many cycles
        repeat(10) @(posedge clk);

        check_result("Value retained after many cycles", 16'h9876);

        // ================================================================
        // TEST 10: Pattern Test
        // ================================================================
        $display("\n--- Test 10: Bit Patterns ---");

        // Test walking 1s
        wr_en = 1;
        wr_val = 16'h0001;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);
        check_result("Pattern 0x0001", 16'h0001);

        wr_en = 1;
        wr_val = 16'h8000;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);
        check_result("Pattern 0x8000", 16'h8000);

        wr_en = 1;
        wr_val = 16'hAAAA;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);
        check_result("Pattern 0xAAAA", 16'hAAAA);

        wr_en = 1;
        wr_val = 16'h5555;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);
        check_result("Pattern 0x5555", 16'h5555);

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
