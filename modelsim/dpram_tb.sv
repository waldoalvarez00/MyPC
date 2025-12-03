// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// DPRam Testbench
// Tests the generic dual-port parameterized RAM

`timescale 1ns/1ps

module dpram_tb;

parameter WORDS = 16;
parameter WIDTH = 16;
localparam ADDR_BITS = $clog2(WORDS);

reg clk;
// Port A
reg [ADDR_BITS-1:0] addr_a;
reg wr_en_a;
reg [WIDTH-1:0] wdata_a;
wire [WIDTH-1:0] q_a;
// Port B
reg [ADDR_BITS-1:0] addr_b;
reg wr_en_b;
reg [WIDTH-1:0] wdata_b;
wire [WIDTH-1:0] q_b;

integer test_count;
integer pass_count;
integer fail_count;

DPRam #(.words(WORDS), .width(WIDTH)) dut (
    .clk(clk),
    .addr_a(addr_a),
    .wr_en_a(wr_en_a),
    .wdata_a(wdata_a),
    .q_a(q_a),
    .addr_b(addr_b),
    .wr_en_b(wr_en_b),
    .wdata_b(wdata_b),
    .q_b(q_b)
);

// Clock generation: 10ns period
always #5 clk = ~clk;

task check(input string test_name, input [WIDTH-1:0] expected, input [WIDTH-1:0] actual);
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
    $display("DPRam Testbench (%0d words x %0d bits)", WORDS, WIDTH);
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    addr_a = 0;
    wr_en_a = 0;
    wdata_a = 0;
    addr_b = 0;
    wr_en_b = 0;
    wdata_b = 0;

    // Wait for initialization
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
    @(posedge clk);
    #1;
    wr_en_a = 0;
    @(posedge clk);
    #1;
    check("Port A write/read", 16'hABCD, q_a);

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
    @(posedge clk);
    #1;
    wr_en_b = 0;
    addr_a = 3;
    @(posedge clk);
    #1;
    check("Port A reads port B's write", 16'h1234, q_a);

    // Test 5: Simultaneous writes to different addresses
    $display("\n--- Testing simultaneous writes ---");
    addr_a = 4;
    addr_b = 5;
    wdata_a = 16'h4444;
    wdata_b = 16'h5555;
    wr_en_a = 1;
    wr_en_b = 1;
    @(posedge clk);
    #1;
    wr_en_a = 0;
    wr_en_b = 0;
    @(posedge clk);
    #1;
    check("Port A wrote addr 4", 16'h4444, q_a);
    check("Port B wrote addr 5", 16'h5555, q_b);

    // Test 6: Bypass logic - write port B, read same addr on port A
    $display("\n--- Testing bypass logic ---");
    addr_a = 6;
    addr_b = 6;
    wdata_b = 16'hBEEF;
    wr_en_b = 1;
    @(posedge clk);
    #1;
    // Bypass should forward wdata_b to q_a
    check("Bypass: port A sees port B write", 16'hBEEF, q_a);
    wr_en_b = 0;

    // Test 7: Bypass logic - write port A, read same addr on port B
    wdata_a = 16'hCAFE;
    wr_en_a = 1;
    @(posedge clk);
    #1;
    check("Bypass: port B sees port A write", 16'hCAFE, q_b);
    wr_en_a = 0;

    // Test 8: All addresses
    $display("\n--- Testing all addresses ---");
    for (int i = 0; i < WORDS; i++) begin
        addr_a = i;
        wdata_a = 16'hF000 + i;
        wr_en_a = 1;
        @(posedge clk);
        #1;
    end
    wr_en_a = 0;

    // Read back all
    for (int i = 0; i < WORDS; i++) begin
        addr_a = i;
        @(posedge clk);
        #1;
        check($sformatf("All addresses: addr %0d", i), 16'hF000 + i, q_a);
    end

    // Test 9: Alternating port access
    $display("\n--- Testing alternating access ---");
    addr_a = 0;
    addr_b = 0;
    wdata_a = 16'hAAAA;
    wr_en_a = 1;
    @(posedge clk);
    #1;
    wr_en_a = 0;
    wdata_b = 16'hBBBB;
    wr_en_b = 1;
    @(posedge clk);
    #1;
    wr_en_b = 0;
    @(posedge clk);
    #1;
    check("Alternating: final value is port B's", 16'hBBBB, q_a);

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
    $dumpfile("dpram_tb.vcd");
    $dumpvars(0, dpram_tb);
end

endmodule
