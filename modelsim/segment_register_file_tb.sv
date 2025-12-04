// ================================================================
// Unit Test for SegmentRegisterFile
// Tests segment register read/write operations and CS port
// ================================================================

`timescale 1ns/1ps

module segment_register_file_tb;

    // Segment register selects (Icarus-compatible, matching RegisterEnum.sv values)
    localparam [1:0] ES = 2'd0;
    localparam [1:0] CS = 2'd1;
    localparam [1:0] SS = 2'd2;
    localparam [1:0] DS = 2'd3;

    // DUT signals
    logic clk;
    logic reset;
    logic [1:0] rd_sel;
    logic [15:0] rd_val;
    logic wr_en;
    logic [1:0] wr_sel;
    logic [15:0] wr_val;
    logic [15:0] cs;

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Variables for procedural use (Icarus compatibility)
    logic [15:0] original_ds;
    logic [15:0] es_val;
    logic [15:0] ds_val;

    // Test values for each segment register
    localparam [15:0] ES_VAL = 16'h00E5;  // Unique value for ES
    localparam [15:0] CS_VAL = 16'h00C5;  // Unique value for CS
    localparam [15:0] SS_VAL = 16'h0055;  // Unique value for SS
    localparam [15:0] DS_VAL = 16'h00D5;  // Unique value for DS

    // Instantiate DUT
    SegmentRegisterFile dut (
        .clk(clk),
        .reset(reset),
        .rd_sel(rd_sel),
        .rd_val(rd_val),
        .wr_en(wr_en),
        .wr_sel(wr_sel),
        .wr_val(wr_val),
        .cs(cs)
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
            fail_count++;
        end
    endtask

    // Main test sequence
    initial begin
        $display("================================================================");
        $display("Segment Register File Unit Test");
        $display("================================================================\n");

        // Initialize
        reset = 0;
        rd_sel = 0;
        wr_en = 0;
        wr_sel = 0;
        wr_val = 0;

        // Allow a few clocks
        repeat(3) @(posedge clk);
        #1;

        // ================================================================
        // TEST 1: Write and Read Back ES
        // ================================================================
        $display("--- Test 1: Write and Read ES ---");

        #1;
        wr_sel = ES;
        wr_val = 16'h1234;
        wr_en = 1;
        #1;
        @(posedge clk);
        #1;
        wr_en = 0;
        #1;

        rd_sel = ES;
        @(posedge clk);
        @(posedge clk);
        #1;

        check_result("ES write/read", rd_val == 16'h1234);

        // ================================================================
        // TEST 2: Write and Read Back CS
        // ================================================================
        $display("\n--- Test 2: Write and Read CS ---");

        #1;
        wr_sel = CS;
        wr_val = 16'h5678;
        wr_en = 1;
        #1;
        @(posedge clk);
        #1;
        wr_en = 0;
        #1;

        rd_sel = CS;
        @(posedge clk);
        @(posedge clk);
        #1;

        check_result("CS write/read", rd_val == 16'h5678);
        check_result("CS port output", cs == 16'h5678);

        // ================================================================
        // TEST 3: Write and Read Back SS
        // ================================================================
        $display("\n--- Test 3: Write and Read SS ---");

        #1;
        wr_sel = SS;
        wr_val = 16'h9ABC;
        wr_en = 1;
        #1;
        @(posedge clk);
        #1;
        wr_en = 0;
        #1;

        rd_sel = SS;
        @(posedge clk);
        @(posedge clk);
        #1;

        check_result("SS write/read", rd_val == 16'h9ABC);

        // ================================================================
        // TEST 4: Write and Read Back DS
        // ================================================================
        $display("\n--- Test 4: Write and Read DS ---");

        #1;
        wr_sel = DS;
        wr_val = 16'hDEF0;
        wr_en = 1;
        #1;
        @(posedge clk);
        #1;
        wr_en = 0;
        #1;

        rd_sel = DS;
        @(posedge clk);
        @(posedge clk);
        #1;

        check_result("DS write/read", rd_val == 16'hDEF0);

        // ================================================================
        // TEST 5: Read Bypass (Write and Read Simultaneously)
        // ================================================================
        $display("\n--- Test 5: Read Bypass ---");

        #1;
        wr_sel = ES;
        wr_val = 16'hABCD;
        wr_en = 1;
        rd_sel = ES;
        #1;
        @(posedge clk);
        @(posedge clk);
        #1;

        check_result("Read bypass (same cycle write/read)", rd_val == 16'hABCD);

        wr_en = 0;
        @(posedge clk);

        // ================================================================
        // TEST 6: Multiple Writes to Same Register
        // ================================================================
        $display("\n--- Test 6: Multiple Writes ---");

        #1;
        wr_sel = CS;
        wr_val = 16'h1111;
        wr_en = 1;
        #1;
        @(posedge clk);

        #1;
        wr_val = 16'h2222;
        #1;
        @(posedge clk);

        #1;
        wr_val = 16'h3333;
        #1;
        @(posedge clk);

        #1;
        wr_en = 0;
        rd_sel = CS;
        @(posedge clk);
        @(posedge clk);
        #1;

        check_result("Multiple writes (last value wins)", rd_val == 16'h3333);
        check_result("CS port tracks writes", cs == 16'h3333);

        // ================================================================
        // TEST 7: Write Without Enable
        // ================================================================
        $display("\n--- Test 7: Write Without Enable ---");

        rd_sel = DS;
        @(posedge clk);
        @(posedge clk);
        #1;
        original_ds = rd_val;

        #1;
        wr_sel = DS;
        wr_val = 16'hFFFF;
        wr_en = 0;  // Write disabled
        #1;
        @(posedge clk);

        rd_sel = DS;
        @(posedge clk);
        @(posedge clk);
        #1;

        check_result("Write without enable (no change)", rd_val == original_ds);

        // ================================================================
        // TEST 8: Independent Register Storage
        // ================================================================
        $display("\n--- Test 8: Independent Registers ---");

        // Write unique values to all registers
        wr_en = 1;

        #1;
        wr_sel = ES;
        wr_val = ES_VAL;
        #1;
        @(posedge clk);

        #1;
        wr_sel = CS;
        wr_val = CS_VAL;
        #1;
        @(posedge clk);

        #1;
        wr_sel = SS;
        wr_val = SS_VAL;
        #1;
        @(posedge clk);

        #1;
        wr_sel = DS;
        wr_val = DS_VAL;
        #1;
        @(posedge clk);

        #1;
        wr_en = 0;
        #1;

        // Read back and verify all
        rd_sel = ES;
        @(posedge clk);
        @(posedge clk);
        #1;
        check_result("ES independent", rd_val == ES_VAL);

        rd_sel = CS;
        @(posedge clk);
        @(posedge clk);
        #1;
        check_result("CS independent", rd_val == CS_VAL);

        rd_sel = SS;
        @(posedge clk);
        @(posedge clk);
        #1;
        check_result("SS independent", rd_val == SS_VAL);

        rd_sel = DS;
        @(posedge clk);
        @(posedge clk);
        #1;
        check_result("DS independent", rd_val == DS_VAL);

        // ================================================================
        // TEST 9: CS Port Always Reflects CS Register
        // ================================================================
        $display("\n--- Test 9: CS Port Tracking ---");

        #1;
        wr_sel = CS;
        wr_en = 1;

        wr_val = 16'hAAAA;
        #1;
        @(posedge clk);
        #1;
        check_result("CS port updates immediately (AAAA)", cs == 16'hAAAA);

        wr_val = 16'h5555;
        #1;
        @(posedge clk);
        #1;
        check_result("CS port updates immediately (5555)", cs == 16'h5555);

        wr_en = 0;
        @(posedge clk);

        // ================================================================
        // TEST 10: Back-to-Back Reads from Different Registers
        // ================================================================
        $display("\n--- Test 10: Back-to-Back Reads ---");

        rd_sel = ES;
        @(posedge clk);
        @(posedge clk);
        #1;
        es_val = rd_val;

        rd_sel = DS;
        @(posedge clk);
        @(posedge clk);
        #1;
        ds_val = rd_val;

        check_result("Back-to-back ES read", es_val == ES_VAL);
        check_result("Back-to-back DS read", ds_val == DS_VAL);

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
