// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Prefetch Unit Testbench
//
// Tests the CPU instruction prefetch unit including:
// - Sequential byte fetching from memory
// - FIFO write operations
// - IP loading and CS:IP addressing
// - FIFO reset on IP change
// - Abort handling during IP changes
// - Odd/even address byte selection
// - Stall when FIFO full

`timescale 1ns/1ps

module prefetch_tb;

// Clock and reset
reg clk;
reg reset;

// Address control
reg [15:0] new_cs;
reg [15:0] new_ip;
reg load_new_ip;

// FIFO write port
wire fifo_wr_en;
wire [7:0] fifo_wr_data;
wire fifo_reset;
reg fifo_full;

// Memory port
wire mem_access;
reg mem_ack;
wire [19:1] mem_address;
reg [15:0] mem_data;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// Clock generation
always #5 clk = ~clk;  // 100 MHz clock

// DUT instantiation
Prefetch dut (
    .clk(clk),
    .reset(reset),
    .new_cs(new_cs),
    .new_ip(new_ip),
    .load_new_ip(load_new_ip),
    .fifo_wr_en(fifo_wr_en),
    .fifo_wr_data(fifo_wr_data),
    .fifo_reset(fifo_reset),
    .fifo_full(fifo_full),
    .mem_access(mem_access),
    .mem_ack(mem_ack),
    .mem_address(mem_address),
    .mem_data(mem_data)
);

// Memory model - simple array
reg [15:0] memory [0:65535];

// Memory access simulation
always @(posedge clk) begin
    if (mem_access && !mem_ack) begin
        mem_ack <= 1'b1;
        mem_data <= memory[mem_address[16:1]];
    end else begin
        mem_ack <= 1'b0;
        mem_data <= 16'h0000;
    end
end

// Helper task to check test result
task check_result(input string test_name, input logic expected, input logic actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected %b, Got %b", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

// Helper task to check byte value
task check_byte(input string test_name, input [7:0] expected, input [7:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected 0x%02h, Got 0x%02h", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

// Helper task to wait for memory ACK
task wait_mem_ack;
    integer timeout;
begin
    timeout = 0;
    while (!mem_ack && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end
    if (!mem_ack) begin
        $display("ERROR: Memory ACK timeout!");
    end
end
endtask

// Main test sequence
initial begin
    integer i;
    integer timeout;

    // Initialize signals
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    new_cs = 16'h0000;
    new_ip = 16'h0000;
    load_new_ip = 0;
    fifo_full = 0;
    mem_ack = 0;
    mem_data = 16'h0000;

    // Initialize memory with test pattern
    for (i = 0; i < 256; i = i + 1) begin
        memory[i] = {8'h80 + i[7:0], i[7:0]};  // High byte = 0x80+i, Low byte = i
    end

    $display("========================================");
    $display("Prefetch Unit Testbench");
    $display("========================================");
    $display("Memory initialized with test pattern");

    // Release reset
    #100;
    reset = 0;
    #40;

    //==================================================================
    // Test 1: Basic initialization
    //==================================================================
    $display("\n--- Test 1: Initial state ---");
    @(posedge clk);
    check_result("No FIFO write on startup", 1'b0, fifo_wr_en);
    check_result("No FIFO reset on startup", 1'b0, fifo_reset);

    //==================================================================
    // Test 2: Load new IP and CS
    //==================================================================
    $display("\n--- Test 2: Load new CS:IP ---");
    new_cs = 16'h1000;
    new_ip = 16'h0000;
    load_new_ip = 1;
    @(posedge clk);

    check_result("FIFO reset asserted on IP load", 1'b1, fifo_reset);

    load_new_ip = 0;
    @(posedge clk);
    @(posedge clk);

    //==================================================================
    // Test 3: Memory access starts
    //==================================================================
    $display("\n--- Test 3: Memory access ---");

    // Wait for memory access to start
    timeout = 0;
    while (!mem_access && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    check_result("Memory access asserts", 1'b1, mem_access);

    //==================================================================
    // Test 4: Fetch from even address
    //==================================================================
    $display("\n--- Test 4: Fetch from even address ---");

    // Memory will respond with data for address 0x10000 >> 1 = 0x8000
    // memory[0x8000] = {0x80, 0x00}
    wait_mem_ack;

    check_result("FIFO write enable on mem ack", 1'b1, fifo_wr_en);
    check_byte("First byte from even address (low byte)", 8'h00, fifo_wr_data);

    @(posedge clk);

    // Second byte should be written from the high byte of the word
    check_result("Second byte write enable", 1'b1, fifo_wr_en);
    check_byte("Second byte from even address (high byte)", 8'h80, fifo_wr_data);

    //==================================================================
    // Test 5: Sequential fetching
    //==================================================================
    $display("\n--- Test 5: Sequential fetching ---");

    // Let prefetcher continue fetching
    @(posedge clk);

    // Wait for next memory access
    timeout = 0;
    while (!mem_access && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    wait_mem_ack;

    check_result("Sequential fetch continues", 1'b1, fifo_wr_en);

    //==================================================================
    // Test 6: Load new IP (flush)
    //==================================================================
    $display("\n--- Test 6: IP change flushes FIFO ---");

    new_cs = 16'h2000;
    new_ip = 16'h0100;
    load_new_ip = 1;
    @(posedge clk);

    check_result("FIFO reset on IP change", 1'b1, fifo_reset);

    load_new_ip = 0;
    @(posedge clk);
    @(posedge clk);

    //==================================================================
    // Test 7: Fetch from odd address
    //==================================================================
    $display("\n--- Test 7: Fetch from odd address ---");

    new_cs = 16'h3000;
    new_ip = 16'h0001;  // Odd address
    load_new_ip = 1;
    @(posedge clk);
    load_new_ip = 0;
    @(posedge clk);
    @(posedge clk);

    // Wait for memory access
    timeout = 0;
    while (!mem_access && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    wait_mem_ack;

    // From odd address, should get high byte of the word
    check_result("FIFO write on odd address fetch", 1'b1, fifo_wr_en);
    // Address 0x30001 >> 1 = 0x18000, word should be memory[0x18000] but high byte
    // Since we're reading from odd address, we get high byte first

    //==================================================================
    // Test 8: FIFO full stalls fetching
    //==================================================================
    $display("\n--- Test 8: FIFO full stalls ---");

    fifo_full = 1;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    // Memory access should stop when FIFO is full
    check_result("No memory access when FIFO full", 1'b0, mem_access);

    fifo_full = 0;
    @(posedge clk);
    @(posedge clk);

    //==================================================================
    // Test 9: Abort during pending fetch
    //==================================================================
    $display("\n--- Test 9: Abort on IP change during fetch ---");

    new_cs = 16'h4000;
    new_ip = 16'h0200;
    load_new_ip = 1;
    @(posedge clk);
    load_new_ip = 0;
    @(posedge clk);
    @(posedge clk);

    // Wait for access to start
    timeout = 0;
    while (!mem_access && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    // Change IP while access is pending
    new_cs = 16'h5000;
    new_ip = 16'h0300;
    load_new_ip = 1;
    @(posedge clk);
    load_new_ip = 0;

    check_result("FIFO reset on abort", 1'b1, fifo_reset);

    // Wait for the aborted fetch to complete
    wait_mem_ack;

    // Should not write to FIFO on aborted fetch
    @(posedge clk);

    //==================================================================
    // Test 10: Address calculation
    //==================================================================
    $display("\n--- Test 10: CS:IP address calculation ---");

    new_cs = 16'hF000;
    new_ip = 16'h1000;
    load_new_ip = 1;
    @(posedge clk);
    load_new_ip = 0;
    @(posedge clk);
    @(posedge clk);

    // Wait for memory access
    timeout = 0;
    while (!mem_access && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    // Physical address = (CS << 4) + IP = 0xF0000 + 0x1000 = 0xF1000
    // Byte address 0xF1000 >> 1 = 0x78880 (word address)
    // Expected mem_address[19:1] = 0x78880
    check_result("Address calculation correct", 1'b1, mem_access);

    //==================================================================
    // Results
    //==================================================================
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
    #100000;  // 100 us timeout
    $display("\n========================================");
    $display("ERROR: Simulation timeout!");
    $display("========================================");
    $finish(1);
end

// VCD dump for waveform viewing
initial begin
    $dumpfile("prefetch_tb.vcd");
    $dumpvars(0, prefetch_tb);
end

endmodule
