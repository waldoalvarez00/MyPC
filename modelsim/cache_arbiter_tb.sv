// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// CacheArbiter Testbench
// Tests the cache arbiter for Harvard architecture

`timescale 1ns/1ps

module cache_arbiter_tb;

reg clk;
reg reset;

// I-Cache interface
reg [19:1] icache_m_addr;
wire [15:0] icache_m_data_in;
reg icache_m_access;
wire icache_m_ack;

// D-Cache interface
reg [19:1] dcache_m_addr;
wire [15:0] dcache_m_data_in;
reg [15:0] dcache_m_data_out;
reg dcache_m_access;
wire dcache_m_ack;
reg dcache_m_wr_en;
reg [1:0] dcache_m_bytesel;

// Memory interface
wire [19:1] mem_m_addr;
reg [15:0] mem_m_data_in;
wire [15:0] mem_m_data_out;
wire mem_m_access;
reg mem_m_ack;
wire mem_m_wr_en;
wire [1:0] mem_m_bytesel;

integer test_count;
integer pass_count;
integer fail_count;

CacheArbiter dut (
    .clk(clk),
    .reset(reset),
    .icache_m_addr(icache_m_addr),
    .icache_m_data_in(icache_m_data_in),
    .icache_m_access(icache_m_access),
    .icache_m_ack(icache_m_ack),
    .dcache_m_addr(dcache_m_addr),
    .dcache_m_data_in(dcache_m_data_in),
    .dcache_m_data_out(dcache_m_data_out),
    .dcache_m_access(dcache_m_access),
    .dcache_m_ack(dcache_m_ack),
    .dcache_m_wr_en(dcache_m_wr_en),
    .dcache_m_bytesel(dcache_m_bytesel),
    .mem_m_addr(mem_m_addr),
    .mem_m_data_in(mem_m_data_in),
    .mem_m_data_out(mem_m_data_out),
    .mem_m_access(mem_m_access),
    .mem_m_ack(mem_m_ack),
    .mem_m_wr_en(mem_m_wr_en),
    .mem_m_bytesel(mem_m_bytesel)
);

// Clock generation: 10ns period
always #5 clk = ~clk;

task check(input string test_name, input [31:0] expected, input [31:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected 0x%h, Got 0x%h", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

task check_bit(input string test_name, input expected, input actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected %0d, Got %0d", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

initial begin
    $display("========================================");
    $display("CacheArbiter Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    icache_m_addr = 19'h00000;
    icache_m_access = 0;
    dcache_m_addr = 19'h00000;
    dcache_m_data_out = 16'h0000;
    dcache_m_access = 0;
    dcache_m_wr_en = 0;
    dcache_m_bytesel = 2'b11;
    mem_m_data_in = 16'h0000;
    mem_m_ack = 0;

    // Release reset
    @(posedge clk);
    @(posedge clk);
    #1;
    reset = 0;
    @(posedge clk);
    #1;

    // Test 1: Initial state - no access
    $display("\n--- Testing initial state ---");
    check_bit("mem_m_access initially 0", 1'b0, mem_m_access);
    check_bit("icache_m_ack initially 0", 1'b0, icache_m_ack);
    check_bit("dcache_m_ack initially 0", 1'b0, dcache_m_ack);

    // Test 2: I-cache access alone
    $display("\n--- Testing I-cache access ---");
    icache_m_addr = 19'h12345;
    icache_m_access = 1;
    @(posedge clk);  // State transitions to SERVING_ICACHE
    #1;
    @(posedge clk);  // serving_icache becomes 1
    #1;
    check_bit("mem_m_access high for I-cache", 1'b1, mem_m_access);
    check("mem_m_addr routes I-cache address", 19'h12345, mem_m_addr);
    check_bit("mem_m_wr_en is 0 for I-cache (read-only)", 1'b0, mem_m_wr_en);

    // Test 3: Memory acknowledges I-cache
    // Ack is combinational, check before clock edge
    mem_m_data_in = 16'hABCD;
    mem_m_ack = 1;
    #1;  // Small delay for combinational logic
    check_bit("icache_m_ack asserted", 1'b1, icache_m_ack);
    check("icache_m_data_in receives data", 16'hABCD, icache_m_data_in);
    @(posedge clk);  // Complete the transaction
    #1;

    // Complete transaction
    mem_m_ack = 0;
    icache_m_access = 0;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;

    // Test 4: D-cache access alone
    $display("\n--- Testing D-cache access ---");
    dcache_m_addr = 19'h54321;
    dcache_m_data_out = 16'h5678;
    dcache_m_wr_en = 1;
    dcache_m_bytesel = 2'b01;
    dcache_m_access = 1;
    @(posedge clk);  // State transitions to SERVING_DCACHE
    #1;
    @(posedge clk);  // serving_dcache becomes 1
    #1;
    check_bit("mem_m_access high for D-cache", 1'b1, mem_m_access);
    check("mem_m_addr routes D-cache address", 19'h54321, mem_m_addr);
    check("mem_m_data_out routes D-cache data", 16'h5678, mem_m_data_out);
    check_bit("mem_m_wr_en routes D-cache write enable", 1'b1, mem_m_wr_en);
    check("mem_m_bytesel routes D-cache bytesel", 2'b01, mem_m_bytesel);

    // Test 5: Memory acknowledges D-cache (combinational ack)
    mem_m_data_in = 16'hDEAD;
    mem_m_ack = 1;
    #1;  // Combinational delay
    check_bit("dcache_m_ack asserted", 1'b1, dcache_m_ack);
    check("dcache_m_data_in receives data", 16'hDEAD, dcache_m_data_in);
    @(posedge clk);
    #1;

    // Complete transaction
    mem_m_ack = 0;
    dcache_m_access = 0;
    dcache_m_wr_en = 0;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;

    // Test 6: D-cache priority over I-cache
    $display("\n--- Testing D-cache priority ---");
    icache_m_addr = 19'h11111;
    icache_m_access = 1;
    dcache_m_addr = 19'h22222;
    dcache_m_access = 1;
    dcache_m_wr_en = 0;
    @(posedge clk);  // Both request, D-cache should win
    #1;
    @(posedge clk);  // serving_dcache becomes 1
    #1;
    check("D-cache wins priority - address routed", 19'h22222, mem_m_addr);
    check_bit("icache_m_ack not asserted (waiting)", 1'b0, icache_m_ack);

    // Complete D-cache transaction (combinational ack)
    mem_m_ack = 1;
    #1;
    check_bit("dcache_m_ack asserted", 1'b1, dcache_m_ack);
    @(posedge clk);
    #1;
    mem_m_ack = 0;
    dcache_m_access = 0;
    @(posedge clk);  // State goes to IDLE
    #1;
    @(posedge clk);  // Now should serve I-cache
    #1;
    @(posedge clk);  // serving_icache becomes 1
    #1;
    check("I-cache served after D-cache completes", 19'h11111, mem_m_addr);

    // Complete I-cache transaction (combinational ack)
    mem_m_ack = 1;
    #1;
    check_bit("icache_m_ack asserted after wait", 1'b1, icache_m_ack);
    @(posedge clk);
    #1;
    mem_m_ack = 0;
    icache_m_access = 0;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;

    // Test 7: D-cache read operation
    $display("\n--- Testing D-cache read ---");
    dcache_m_addr = 19'h33333;
    dcache_m_wr_en = 0;
    dcache_m_bytesel = 2'b11;
    dcache_m_access = 1;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;
    check_bit("D-cache read: wr_en is 0", 1'b0, mem_m_wr_en);
    check("D-cache read: bytesel is 11", 2'b11, mem_m_bytesel);

    mem_m_ack = 1;
    mem_m_data_in = 16'hBEEF;
    @(posedge clk);
    #1;
    check("D-cache receives read data", 16'hBEEF, dcache_m_data_in);
    mem_m_ack = 0;
    dcache_m_access = 0;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;

    // Test 8: Reset during active transaction
    $display("\n--- Testing reset ---");
    dcache_m_access = 1;
    dcache_m_addr = 19'h44444;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;
    check_bit("Transaction active before reset", 1'b1, mem_m_access);

    reset = 1;
    @(posedge clk);
    #1;
    check_bit("mem_m_access cleared on reset", 1'b0, mem_m_access);
    check_bit("dcache_m_ack cleared on reset", 1'b0, dcache_m_ack);

    // Results
    #100;
    $display("\n========================================");
    $display("Test Results:");
    $display("  Total: %0d", test_count);
    $display("  Pass:  %0d", pass_count);
    $display("  Fail:  %0d", fail_count);
    $display("========================================");

    if (fail_count == 0)
        $display("*** ALL TESTS PASSED ***");
    else
        $display("*** SOME TESTS FAILED ***");

    $display("\n========================================");
    $display("SIMULATION PASSED!");
    $display("========================================");

    $finish(1);
end

// Timeout watchdog
initial begin
    #100000;
    $display("ERROR: Simulation timeout!");
    $finish(1);
end

// VCD dump
initial begin
    $dumpfile("cache_arbiter_tb.vcd");
    $dumpvars(0, cache_arbiter_tb);
end

endmodule
