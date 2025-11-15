`timescale 1ns/1ps

module immediate_reader_tb;

// DUT signals
logic clk;
logic reset;
logic start;
logic flush;
logic busy;
logic complete;
logic is_8bit;
logic [15:0] immediate;
logic fifo_rd_en;
logic [7:0] fifo_rd_data;
logic fifo_empty;

// Test FIFO
logic [7:0] test_fifo[16];
integer fifo_rd_ptr;

// Test counters
integer test_count = 0;
integer pass_count = 0;
integer fail_count = 0;

// Test variables
logic [15:0] first_val;
logic [15:0] second_val;

// Instantiate DUT
ImmediateReader dut (
    .clk(clk),
    .reset(reset),
    .start(start),
    .flush(flush),
    .busy(busy),
    .complete(complete),
    .is_8bit(is_8bit),
    .immediate(immediate),
    .fifo_rd_en(fifo_rd_en),
    .fifo_rd_data(fifo_rd_data),
    .fifo_empty(fifo_empty)
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;
end

// FIFO simulation logic
always @(posedge clk) begin
    if (reset || flush) begin
        fifo_rd_ptr = 0;
    end else if (fifo_rd_en && !fifo_empty) begin
        fifo_rd_data = test_fifo[fifo_rd_ptr];
        fifo_rd_ptr = fifo_rd_ptr + 1;
    end
end

always @(*) begin
    fifo_empty = (fifo_rd_ptr >= 16) || (test_fifo[fifo_rd_ptr] === 8'hxx);
end

task check_result(input string test_name, input logic condition);
    test_count++;
    if (condition) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count++;
    end else begin
        $display("[FAIL] Test %0d: %s", test_count, test_name);
        $display("        immediate=0x%04h, busy=%b, complete=%b",
                 immediate, busy, complete);
        fail_count++;
    end
endtask

// Main test sequence
initial begin
    $display("========================================");
    $display("ImmediateReader Unit Test");
    $display("========================================\n");

    // Initialize
    reset = 1;
    start = 0;
    flush = 0;
    is_8bit = 0;
    fifo_rd_ptr = 0;

    // Initialize FIFO with test data
    for (int i = 0; i < 16; i++) test_fifo[i] = 8'hxx;

    repeat(3) @(posedge clk);
    reset = 0;
    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 1: 8-bit Immediate (Positive Value)
    // ================================================================
    $display("--- Test 1: 8-bit Immediate (Positive) ---");

    // Setup FIFO
    fifo_rd_ptr = 0;
    test_fifo[0] = 8'h42;  // Positive value
    test_fifo[1] = 8'hxx;

    is_8bit = 1;
    start = 1;
    @(posedge clk);
    start = 0;

    // Wait for complete
    repeat(5) @(posedge clk);

    check_result("8-bit positive immediate",
                 immediate == 16'h0042 && complete);

    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 2: 8-bit Immediate (Negative Value - Sign Extended)
    // ================================================================
    $display("\n--- Test 2: 8-bit Immediate (Negative) ---");

    fifo_rd_ptr = 0;
    test_fifo[0] = 8'hFF;  // -1 in signed 8-bit
    test_fifo[1] = 8'hxx;

    is_8bit = 1;
    start = 1;
    @(posedge clk);
    start = 0;

    repeat(5) @(posedge clk);

    check_result("8-bit negative immediate (sign extended)",
                 immediate == 16'hFFFF && complete);

    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 3: 16-bit Immediate (Little Endian)
    // ================================================================
    $display("\n--- Test 3: 16-bit Immediate ---");

    fifo_rd_ptr = 0;
    test_fifo[0] = 8'h34;  // Low byte
    test_fifo[1] = 8'h12;  // High byte
    test_fifo[2] = 8'hxx;

    is_8bit = 0;
    start = 1;
    @(posedge clk);
    start = 0;

    repeat(10) @(posedge clk);

    check_result("16-bit immediate (little endian)",
                 immediate == 16'h1234 && complete);

    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 4: Busy Signal
    // ================================================================
    $display("\n--- Test 4: Busy Signal ---");

    fifo_rd_ptr = 0;
    test_fifo[0] = 8'hAB;
    test_fifo[1] = 8'hCD;
    test_fifo[2] = 8'hxx;

    is_8bit = 0;
    start = 1;
    @(posedge clk);

    check_result("Busy asserted during fetch", busy == 1);

    start = 0;
    repeat(10) @(posedge clk);

    check_result("Busy deasserted after complete", busy == 0 && complete);

    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 5: Flush Operation
    // ================================================================
    $display("\n--- Test 5: Flush Operation ---");

    fifo_rd_ptr = 0;
    test_fifo[0] = 8'h12;
    test_fifo[1] = 8'h34;
    test_fifo[2] = 8'hxx;

    is_8bit = 0;
    start = 1;
    @(posedge clk);
    start = 0;
    @(posedge clk);

    // Flush before complete
    flush = 1;
    @(posedge clk);
    flush = 0;
    @(posedge clk);

    check_result("Flush clears busy", busy == 0);
    check_result("Flush clears complete", complete == 0);

    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 6: Sequential Reads
    // ================================================================
    $display("\n--- Test 6: Sequential Reads ---");

    fifo_rd_ptr = 0;
    test_fifo[0] = 8'h11;
    test_fifo[1] = 8'h22;
    test_fifo[2] = 8'h33;
    test_fifo[3] = 8'hxx;

    // First 8-bit read
    is_8bit = 1;
    start = 1;
    @(posedge clk);
    start = 0;
    repeat(5) @(posedge clk);

    first_val = immediate;

    // Second 8-bit read
    is_8bit = 1;
    start = 1;
    @(posedge clk);
    start = 0;
    repeat(5) @(posedge clk);

    second_val = immediate;

    check_result("First sequential read", first_val == 16'h0011);
    check_result("Second sequential read", second_val == 16'h0022);

    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 7: Zero Value
    // ================================================================
    $display("\n--- Test 7: Zero Value ---");

    fifo_rd_ptr = 0;
    test_fifo[0] = 8'h00;
    test_fifo[1] = 8'hxx;

    is_8bit = 1;
    start = 1;
    @(posedge clk);
    start = 0;
    repeat(5) @(posedge clk);

    check_result("Zero immediate value", immediate == 16'h0000 && complete);

    repeat(2) @(posedge clk);

    // ================================================================
    // TEST 8: Complete Signal Timing
    // ================================================================
    $display("\n--- Test 8: Complete Signal Timing ---");

    fifo_rd_ptr = 0;
    test_fifo[0] = 8'h55;
    test_fifo[1] = 8'hxx;

    is_8bit = 1;
    start = 1;
    @(posedge clk);

    // Complete should not be asserted immediately
    check_result("Complete not immediate", complete == 0);

    start = 0;
    @(posedge clk);

    // Should be complete after reading 1 byte for 8-bit
    check_result("Complete after byte read", complete == 1);

    repeat(2) @(posedge clk);

    // ================================================================
    // Summary
    // ================================================================
    $display("\n========================================");
    $display("TEST SUMMARY");
    $display("========================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Pass Rate:   %0d%%", (pass_count * 100) / test_count);
    $display("========================================");

    if (fail_count == 0) begin
        $display("✓ ALL TESTS PASSED\n");
        $finish(0);
    end else begin
        $display("✗ SOME TESTS FAILED\n");
        $finish(1);
    end
end

endmodule
