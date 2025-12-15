// ================================================================
// Unit Test for Fifo
// Tests FIFO queue functionality (write, read, flush, full/empty)
// ================================================================

`timescale 1ns/1ps

module fifo_tb;

    // Parameters matching DUT defaults
    parameter DATA_WIDTH = 16;
    parameter DEPTH = 8;
    parameter FULL_THRESHOLD = 2;

    // DUT signals
    logic clk;
    logic reset;
    logic flush;
    logic wr_en;
    logic [DATA_WIDTH-1:0] wr_data;
    logic rd_en;
    logic [DATA_WIDTH-1:0] rd_data;
    logic empty;
    logic nearly_full;
    logic full;

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Instantiate DUT
    Fifo #(
        .data_width(DATA_WIDTH),
        .depth(DEPTH),
        .full_threshold(FULL_THRESHOLD)
    ) dut (
        .clk(clk),
        .reset(reset),
        .flush(flush),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .rd_en(rd_en),
        .rd_data(rd_data),
        .empty(empty),
        .nearly_full(nearly_full),
        .full(full)
    );

    // Clock generation: 50 MHz
    initial begin
        clk = 0;
        forever #10 clk = ~clk;
    end

    task check_result(input string test_name, input logic condition);
        test_count++;
        if (condition) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s", test_count, test_name);
            $display("        empty=%b, nearly_full=%b, full=%b",
                     empty, nearly_full, full);
            fail_count++;
        end
    endtask

    // Main test sequence
    initial begin
        $display("================================================================");
        $display("Fifo Unit Test (depth=%0d, data_width=%0d)",
                 DEPTH, DATA_WIDTH);
        $display("================================================================\n");

        // Initialize
        reset = 1;
        flush = 0;
        wr_en = 0;
        wr_data = 0;
        rd_en = 0;

        repeat(3) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        // ================================================================
        // TEST 1: Reset State
        // ================================================================
        $display("--- Test 1: Reset State ---");

        check_result("Empty after reset", empty == 1);
        check_result("Not full after reset", full == 0);
        check_result("Not nearly full after reset", nearly_full == 0);

        // ================================================================
        // TEST 2: Write Single Entry
        // ================================================================
        $display("\n--- Test 2: Write Single Entry ---");

        wr_en = 1;
        wr_data = 16'h1234;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("Not empty after write", empty == 0);
        check_result("Not full after single write", full == 0);

        // ================================================================
        // TEST 3: Read Single Entry
        // ================================================================
        $display("\n--- Test 3: Read Single Entry ---");

        rd_en = 1;
        @(posedge clk);
        rd_en = 0;
        @(posedge clk);

        check_result("Read correct data", rd_data == 16'h1234);
        check_result("Empty after reading last entry", empty == 1);

        // ================================================================
        // TEST 4: Write Multiple Entries
        // ================================================================
        $display("\n--- Test 4: Write Multiple Entries ---");

        wr_en = 1;
        for (int i = 0; i < 4; i++) begin
            wr_data = 16'h1000 + i;
            @(posedge clk);
        end
        wr_en = 0;
        @(posedge clk);

        check_result("Not empty after 4 writes", empty == 0);
        check_result("Not full after 4 writes (depth=8)", full == 0);

        // ================================================================
        // TEST 5: Read Multiple Entries (FIFO Order)
        // ================================================================
        $display("\n--- Test 5: FIFO Order ---");

        rd_en = 1;
        @(posedge clk);
        check_result("First read = 0x1000", rd_data == 16'h1000);

        @(posedge clk);
        check_result("Second read = 0x1001", rd_data == 16'h1001);

        @(posedge clk);
        check_result("Third read = 0x1002", rd_data == 16'h1002);

        @(posedge clk);
        check_result("Fourth read = 0x1003", rd_data == 16'h1003);

        rd_en = 0;
        @(posedge clk);

        check_result("Empty after reading all 4", empty == 1);

        // ================================================================
        // TEST 6: Fill FIFO Completely
        // ================================================================
        $display("\n--- Test 6: Fill to Capacity ---");

        wr_en = 1;
        for (int i = 0; i < DEPTH; i++) begin
            wr_data = 16'h2000 + i;
            @(posedge clk);
        end
        wr_en = 0;
        @(posedge clk);

        check_result("Full after writing DEPTH entries", full == 1);
        check_result("Not empty when full", empty == 0);

        // ================================================================
        // TEST 7: Write to Full FIFO (Should Not Overflow)
        // ================================================================
        $display("\n--- Test 7: Write When Full ---");

        wr_en = 1;
        wr_data = 16'hDEAD;  // This should not be written
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("Still full after write attempt", full == 1);

        // Drain FIFO and check no overflow occurred
        rd_en = 1;
        for (int i = 0; i < DEPTH; i++) begin
            @(posedge clk);
            if (i < DEPTH) begin
                if (rd_data != (16'h2000 + i)) begin
                    $display("[ERROR] Read 0x%04h, expected 0x%04h at index %0d",
                             rd_data, 16'h2000 + i, i);
                end
            end
        end
        rd_en = 0;
        @(posedge clk);

        check_result("Empty after draining full FIFO", empty == 1);

        // ================================================================
        // TEST 8: Nearly Full Threshold
        // ================================================================
        $display("\n--- Test 8: Nearly Full Flag ---");

        wr_en = 1;
        for (int i = 0; i < (DEPTH - FULL_THRESHOLD - 1); i++) begin
            wr_data = 16'h3000 + i;
            @(posedge clk);
        end
        wr_en = 0;
        @(posedge clk);

        check_result("Not nearly full yet", nearly_full == 0);

        // Write one more to trigger nearly_full
        wr_en = 1;
        wr_data = 16'h3FFF;
        @(posedge clk);
        wr_en = 0;
        @(posedge clk);

        check_result("Nearly full triggered", nearly_full == 1);

        // Flush for next test
        flush = 1;
        @(posedge clk);
        flush = 0;
        @(posedge clk);

        // ================================================================
        // TEST 9: Flush Operation
        // ================================================================
        $display("\n--- Test 9: Flush ---");

        // Fill with some data
        wr_en = 1;
        for (int i = 0; i < 5; i++) begin
            wr_data = 16'h4000 + i;
            @(posedge clk);
        end
        wr_en = 0;
        @(posedge clk);

        check_result("Not empty before flush", empty == 0);

        // Flush
        flush = 1;
        @(posedge clk);
        flush = 0;
        @(posedge clk);

        check_result("Empty after flush", empty == 1);
        check_result("Not full after flush", full == 0);

        // ================================================================
        // TEST 10: Simultaneous Read and Write
        // ================================================================
        $display("\n--- Test 10: Simultaneous Read/Write ---");

        // Write some initial data
        wr_en = 1;
        for (int i = 0; i < 3; i++) begin
            wr_data = 16'h5000 + i;
            @(posedge clk);
        end

        // Now read and write simultaneously
        rd_en = 1;
        wr_data = 16'h5003;
        @(posedge clk);

        check_result("Read first value", rd_data == 16'h5000);
        check_result("Count stable with simultaneous rd/wr", empty == 0);

        rd_en = 0;
        wr_en = 0;
        @(posedge clk);

        // Flush for next test
        flush = 1;
        @(posedge clk);
        flush = 0;
        @(posedge clk);

        // ================================================================
        // TEST 11: Read From Empty FIFO
        // ================================================================
        $display("\n--- Test 11: Read When Empty ---");

        check_result("FIFO is empty", empty == 1);

        rd_en = 1;
        @(posedge clk);
        @(posedge clk);
        rd_en = 0;
        @(posedge clk);

        check_result("Still empty after read attempts", empty == 1);

        // ================================================================
        // TEST 12: Wrap-Around (Circular Buffer)
        // ================================================================
        $display("\n--- Test 12: Wrap-Around ---");

        // Fill halfway
        wr_en = 1;
        for (int i = 0; i < (DEPTH/2); i++) begin
            wr_data = 16'h6000 + i;
            @(posedge clk);
        end
        wr_en = 0;

        // Read halfway
        rd_en = 1;
        for (int i = 0; i < (DEPTH/2); i++) begin
            @(posedge clk);
        end
        rd_en = 0;
        @(posedge clk);

        // Write more to cause wrap
        wr_en = 1;
        for (int i = 0; i < DEPTH; i++) begin
            wr_data = 16'h7000 + i;
            @(posedge clk);
        end
        wr_en = 0;
        @(posedge clk);

        check_result("Full after wrap-around write", full == 1);

        // Verify FIFO order
        rd_en = 1;
        @(posedge clk);
        check_result("First after wrap = 0x7000", rd_data == 16'h7000);
        rd_en = 0;

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
