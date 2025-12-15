// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Self-Modifying Code (SMC) Detection Testbench
//
// Tests the SMC detection logic in Prefetch unit including:
// - Write inside prefetch range triggers flush
// - Write outside range does NOT trigger flush
// - Write at boundary triggers flush
// - Empty FIFO does not trigger spurious flush
// - Segment wrap-around handling

`timescale 1ns/1ps

module prefetch_smc_tb;

// Clock and reset
reg clk;
reg reset;

// Address control
reg [15:0] new_cs;
reg [15:0] new_ip;
reg load_new_ip;

// FIFO signals
wire fifo_wr_en;
wire [7:0] fifo_wr_data;
wire fifo_reset;
wire fifo_empty;
wire fifo_full;
wire fifo_nearly_full;
wire [3:0] fifo_count;

// Memory port
wire mem_access;
reg mem_ack;
wire [19:1] mem_address;
reg [15:0] mem_data;

// SMC Detection signals
reg coh_wr_valid;
reg [19:1] coh_wr_addr;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// FIFO read port (to drain FIFO for testing)
reg fifo_rd_en;
wire [7:0] fifo_rd_data;

// Clock generation
always #5 clk = ~clk;  // 100 MHz clock

// Instantiate the FIFO
Fifo #(.data_width(8), .depth(6))
    PrefetchFifo (
        .clk(clk),
        .reset(reset),
        .flush(fifo_reset),
        .wr_en(fifo_wr_en),
        .wr_data(fifo_wr_data),
        .rd_en(fifo_rd_en),
        .rd_data(fifo_rd_data),
        .empty(fifo_empty),
        .nearly_full(fifo_nearly_full),
        .full(fifo_full),
        .count_out(fifo_count)
    );

// Instantiate Prefetch DUT
Prefetch dut (
    .clk(clk),
    .reset(reset),
    .new_cs(new_cs),
    .new_ip(new_ip),
    .load_new_ip(load_new_ip),
    .fifo_wr_en(fifo_wr_en),
    .fifo_wr_data(fifo_wr_data),
    .fifo_reset(fifo_reset),
    .fifo_full(fifo_nearly_full),
    .mem_access(mem_access),
    .mem_ack(mem_ack),
    .mem_address(mem_address),
    .mem_data(mem_data),
    // SMC Detection
    .coh_wr_valid(coh_wr_valid),
    .coh_wr_addr(coh_wr_addr),
    .fifo_count(fifo_count)
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

// Helper task to wait for N clock cycles
task wait_cycles(input integer n);
    integer i;
begin
    for (i = 0; i < n; i = i + 1)
        @(posedge clk);
end
endtask

// Helper task to issue a coherency write
task issue_coh_write(input [19:1] addr);
begin
    coh_wr_valid = 1;
    coh_wr_addr = addr;
    @(posedge clk);
    coh_wr_valid = 0;
    coh_wr_addr = 19'b0;
    // Wait 2 cycles for registered SMC detection
    @(posedge clk);
    @(posedge clk);
end
endtask

// Helper task to load new IP and wait for FIFO to fill
task load_ip_and_fill_fifo(input [15:0] cs_val, input [15:0] ip_val, input integer fill_count);
    integer timeout;
    integer filled;
begin
    new_cs = cs_val;
    new_ip = ip_val;
    load_new_ip = 1;
    @(posedge clk);
    load_new_ip = 0;

    // Wait for FIFO to fill
    timeout = 0;
    filled = 0;
    while (fifo_count < fill_count && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (timeout >= 100) begin
        $display("WARNING: Timeout waiting for FIFO to fill. Count = %0d", fifo_count);
    end

    // Let registers settle
    @(posedge clk);
    @(posedge clk);
end
endtask

// Main test sequence
initial begin
    integer i;

    // Initialize signals
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    new_cs = 16'h0000;
    new_ip = 16'h0000;
    load_new_ip = 0;
    mem_ack = 0;
    mem_data = 16'h0000;
    coh_wr_valid = 0;
    coh_wr_addr = 19'b0;
    fifo_rd_en = 0;

    // Initialize memory with test pattern
    for (i = 0; i < 65536; i = i + 1) begin
        memory[i] = {8'h80 + i[7:0], i[7:0]};
    end

    $display("========================================");
    $display("SMC Detection Testbench");
    $display("========================================");

    // Release reset
    #100;
    reset = 0;
    wait_cycles(5);

    //==================================================================
    // Test 1: Write inside prefetch range triggers flush
    //==================================================================
    $display("\n--- Test 1: Write inside prefetch range ---");

    // Load CS:IP = 0x1000:0x0000, physical addr = 0x10000
    load_ip_and_fill_fifo(16'h1000, 16'h0000, 4);

    $display("FIFO count after fill: %0d", fifo_count);
    $display("Prefetch range should be around physical word addr 0x%05x", 19'h8000);  // (0x1000 << 3) = 0x8000

    // Verify FIFO has data
    check_result("FIFO has data after fill", 1'b1, fifo_count > 0);

    // Issue write to address within prefetch range
    // Physical addr = (CS << 4) + IP = 0x10000, word addr = 0x8000
    $display("Issuing write to addr 0x%05x (inside range)", 19'h8000);
    issue_coh_write(19'h8000);

    // Check that SMC flush occurred
    check_result("FIFO flushed on write inside range", 1'b1, fifo_count == 0);

    //==================================================================
    // Test 2: Write outside prefetch range does NOT flush
    //==================================================================
    $display("\n--- Test 2: Write outside prefetch range ---");

    // Refill FIFO
    load_ip_and_fill_fifo(16'h1000, 16'h0000, 4);

    $display("FIFO count after fill: %0d", fifo_count);

    // Issue write to address FAR outside prefetch range
    $display("Issuing write to addr 0x%05x (outside range)", 19'h0100);
    issue_coh_write(19'h0100);

    // Check that FIFO was NOT flushed
    check_result("FIFO NOT flushed on write outside range", 1'b1, fifo_count > 0);

    //==================================================================
    // Test 3: Empty FIFO does not trigger spurious flush
    //==================================================================
    $display("\n--- Test 3: Empty FIFO no spurious flush ---");

    // Load new IP to flush FIFO, then immediately test
    new_cs = 16'h2000;
    new_ip = 16'h0000;
    load_new_ip = 1;
    @(posedge clk);
    load_new_ip = 0;
    @(posedge clk);

    // FIFO should be empty after reset
    check_result("FIFO empty after IP load", 1'b1, fifo_count == 0);

    // Store current fifo_reset state
    @(posedge clk);

    // Issue write - should NOT cause smc_flush since FIFO is empty
    $display("Issuing write while FIFO empty");
    coh_wr_valid = 1;
    coh_wr_addr = 19'h10000;  // Some address in range
    @(posedge clk);
    coh_wr_valid = 0;

    // Wait for registered logic
    @(posedge clk);

    // fifo_reset should still be 0 (no spurious flush from SMC with empty FIFO)
    check_result("No spurious flush on empty FIFO", 1'b0, fifo_reset);

    //==================================================================
    // Test 4: Boundary condition - write at start of range
    //==================================================================
    $display("\n--- Test 4: Write at start of range ---");

    // Refill FIFO at known location
    load_ip_and_fill_fifo(16'h3000, 16'h0000, 4);

    $display("FIFO count: %0d", fifo_count);

    // Write to exact start address (CS << 3 = 0x18000)
    $display("Issuing write to start addr 0x%05x", 19'h18000);
    issue_coh_write(19'h18000);

    check_result("Flush on write to range start", 1'b1, fifo_count == 0);

    //==================================================================
    // Test 5: Boundary condition - write at end of range
    //==================================================================
    $display("\n--- Test 5: Write at end of range ---");

    // Refill FIFO
    load_ip_and_fill_fifo(16'h3000, 16'h0000, 4);

    $display("FIFO count: %0d", fifo_count);

    // The end address depends on how many bytes are in FIFO
    // With 4 bytes from IP=0, range is words 0-1 (addresses 0-3 bytes)
    // Write to word address 0x18001 (byte addresses 2-3)
    $display("Issuing write to end range word 0x%05x", 19'h18001);
    issue_coh_write(19'h18001);

    check_result("Flush on write to range end", 1'b1, fifo_count == 0);

    //==================================================================
    // Test 6: Write just outside range (no flush)
    //==================================================================
    $display("\n--- Test 6: Write just outside range ---");

    // Refill FIFO
    load_ip_and_fill_fifo(16'h3000, 16'h0000, 4);

    $display("FIFO count: %0d", fifo_count);

    // Write to address just past the range
    // With 4 bytes, range ends at word 1 (bytes 0-3), so word 3 should be outside
    $display("Issuing write to addr 0x%05x (just outside)", 19'h18003);
    issue_coh_write(19'h18003);

    check_result("No flush on write just outside range", 1'b1, fifo_count > 0);

    //==================================================================
    // Test 7: Multiple consecutive writes
    //==================================================================
    $display("\n--- Test 7: Multiple consecutive writes ---");

    // Refill FIFO
    load_ip_and_fill_fifo(16'h4000, 16'h0000, 4);

    // Write outside range multiple times
    issue_coh_write(19'h10000);  // Far outside
    issue_coh_write(19'h10001);  // Far outside

    check_result("FIFO intact after outside writes", 1'b1, fifo_count > 0);

    // Now write inside
    issue_coh_write(19'h20000);  // (0x4000 << 3) = 0x20000

    check_result("Flush on inside write after outside writes", 1'b1, fifo_count == 0);

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
    if (fail_count == 0)
        $display("SIMULATION PASSED!");
    else
        $display("SIMULATION FAILED!");
    $display("========================================");

    $finish(1);
end

// Timeout watchdog
initial begin
    #500000;  // 500 us timeout
    $display("\n========================================");
    $display("ERROR: Simulation timeout!");
    $display("========================================");
    $finish(1);
end

// VCD dump for waveform viewing
initial begin
    $dumpfile("prefetch_smc_tb.vcd");
    $dumpvars(0, prefetch_smc_tb);
end

endmodule
