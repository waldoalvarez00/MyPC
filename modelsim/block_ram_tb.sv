// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// BlockRam Testbench
// Tests the dual-port block RAM with byte enables

`timescale 1ns/1ps

module block_ram_tb;

parameter WORDS = 16;
localparam ADDR_BITS = $clog2(WORDS);

reg clk;
// Port A
reg [ADDR_BITS-1:0] addr_a;
reg wr_en_a;
reg [1:0] be_a;
reg [15:0] wdata_a;
wire [15:0] q_a;
// Port B
reg [ADDR_BITS-1:0] addr_b;
reg wr_en_b;
reg [1:0] be_b;
reg [15:0] wdata_b;
wire [15:0] q_b;

integer test_count;
integer pass_count;
integer fail_count;

BlockRam #(.words(WORDS)) dut (
    .clk(clk),
    .addr_a(addr_a),
    .wr_en_a(wr_en_a),
    .be_a(be_a),
    .wdata_a(wdata_a),
    .q_a(q_a),
    .addr_b(addr_b),
    .wr_en_b(wr_en_b),
    .be_b(be_b),
    .wdata_b(wdata_b),
    .q_b(q_b)
);

// Clock generation: 10ns period
always #5 clk = ~clk;

task check(input string test_name, input [15:0] expected, input [15:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected 0x%04h, Got 0x%04h", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

initial begin
    $display("========================================");
    $display("BlockRam Testbench (%0d words)", WORDS);
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    addr_a = 0;
    wr_en_a = 0;
    be_a = 2'b11;
    wdata_a = 16'h0000;
    addr_b = 0;
    wr_en_b = 0;
    be_b = 2'b11;
    wdata_b = 16'h0000;

    // Wait a few cycles for initialization
    @(posedge clk);
    @(posedge clk);
    #1;

    // Test 1: Initial read (should be 0)
    $display("\n--- Testing initial state ---");
    addr_a = 0;
    addr_b = 1;
    @(posedge clk);
    #1;
    check("Initial read port A addr 0", 16'h0000, q_a);
    check("Initial read port B addr 1", 16'h0000, q_b);

    // Test 2: Write via port A, read via port A
    $display("\n--- Testing port A write/read ---");
    addr_a = 2;
    wdata_a = 16'hABCD;
    wr_en_a = 1;
    be_a = 2'b11;
    @(posedge clk);
    #1;
    wr_en_a = 0;
    @(posedge clk);
    #1;
    check("Port A write/read full word", 16'hABCD, q_a);

    // Test 3: Read same address via port B
    addr_b = 2;
    @(posedge clk);
    #1;
    check("Port B reads port A's write", 16'hABCD, q_b);

    // Test 4: Write via port B, read via port A
    $display("\n--- Testing port B write/read ---");
    addr_b = 3;
    wdata_b = 16'h1234;
    wr_en_b = 1;
    be_b = 2'b11;
    @(posedge clk);
    #1;
    wr_en_b = 0;
    addr_a = 3;
    @(posedge clk);
    #1;
    check("Port A reads port B's write", 16'h1234, q_a);

    // Test 5: Byte enable - write low byte only
    $display("\n--- Testing byte enables ---");
    addr_a = 4;
    wdata_a = 16'hFFFF;
    wr_en_a = 1;
    be_a = 2'b11;
    @(posedge clk);
    #1;
    // Now write low byte only
    wdata_a = 16'h0012;
    be_a = 2'b01;
    @(posedge clk);
    #1;
    wr_en_a = 0;
    be_a = 2'b11;
    @(posedge clk);
    #1;
    check("Low byte only write", 16'hFF12, q_a);

    // Test 6: Byte enable - write high byte only
    wdata_a = 16'h3400;
    be_a = 2'b10;
    wr_en_a = 1;
    @(posedge clk);
    #1;
    wr_en_a = 0;
    be_a = 2'b11;
    @(posedge clk);
    #1;
    check("High byte only write", 16'h3412, q_a);

    // Test 7: Simultaneous write to different addresses
    $display("\n--- Testing simultaneous writes ---");
    addr_a = 5;
    addr_b = 6;
    wdata_a = 16'h5555;
    wdata_b = 16'h6666;
    wr_en_a = 1;
    wr_en_b = 1;
    be_a = 2'b11;
    be_b = 2'b11;
    @(posedge clk);
    #1;
    wr_en_a = 0;
    wr_en_b = 0;
    @(posedge clk);
    #1;
    check("Port A writes addr 5", 16'h5555, q_a);
    check("Port B writes addr 6", 16'h6666, q_b);

    // Test 8: Bypass logic - write port B, read same addr on port A
    $display("\n--- Testing bypass logic ---");
    addr_a = 7;
    addr_b = 7;
    wdata_b = 16'hBEEF;
    wr_en_b = 1;
    @(posedge clk);
    #1;
    // Bypass should forward wdata_b to q_a
    check("Bypass: port A sees port B write (same cycle)", 16'hBEEF, q_a);
    wr_en_b = 0;

    // Test 9: Bypass logic - write port A, read same addr on port B
    wdata_a = 16'hCAFE;
    wr_en_a = 1;
    @(posedge clk);
    #1;
    check("Bypass: port B sees port A write (same cycle)", 16'hCAFE, q_b);
    wr_en_a = 0;

    // Test 10: Sequential access pattern
    $display("\n--- Testing sequential access ---");
    for (int i = 0; i < 8; i++) begin
        addr_a = i;
        wdata_a = 16'h1000 + i;
        wr_en_a = 1;
        @(posedge clk);
        #1;
    end
    wr_en_a = 0;

    // Read back
    for (int i = 0; i < 8; i++) begin
        addr_a = i;
        @(posedge clk);
        #1;
        check($sformatf("Sequential write/read addr %0d", i), 16'h1000 + i, q_a);
    end

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
    $dumpfile("block_ram_tb.vcd");
    $dumpvars(0, block_ram_tb);
end

endmodule
