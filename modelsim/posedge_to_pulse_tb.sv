// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// PosedgeToPulse Testbench
// Tests the edge detector that generates a single pulse on rising edge

`timescale 1ns/1ps

module posedge_to_pulse_tb;

reg clk;
reg reset;
reg d;
wire q;

integer test_count;
integer pass_count;
integer fail_count;

// Clock generation
always #5 clk = ~clk;

// DUT instantiation
PosedgeToPulse dut (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q)
);

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

initial begin
    $display("========================================");
    $display("PosedgeToPulse Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    d = 0;

    // Release reset
    #20;
    reset = 0;
    #20;

    // Test 1: Output should be 0 when d is low
    @(posedge clk);
    #1;
    check_result("Output 0 when d is low", 1'b0, q);

    // Test 2: Rising edge of d generates pulse
    // q = (d ^ d_prev) & d, so pulse appears on FIRST clock after d goes high
    d = 1;
    @(posedge clk);  // d=1, d_prev was 0, so q = (1^0)&1 = 1
    #1;
    check_result("Pulse generated on rising edge", 1'b1, q);

    // Test 3: Pulse lasts only one cycle
    @(posedge clk);
    #1;
    check_result("Pulse lasts only one cycle", 1'b0, q);

    // Test 4: No pulse when d stays high
    @(posedge clk);
    #1;
    check_result("No pulse when d stays high", 1'b0, q);

    // Test 5: Falling edge doesn't generate pulse
    d = 0;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("No pulse on falling edge", 1'b0, q);

    // Test 6: Another rising edge generates another pulse
    d = 1;
    @(posedge clk);  // Pulse on first clock after d goes high
    #1;
    check_result("Second rising edge generates pulse", 1'b1, q);

    // Test 7: Reset clears output
    reset = 1;
    @(posedge clk);
    #1;
    check_result("Reset clears output", 1'b0, q);

    // Test 8: Rising edge after reset generates pulse
    reset = 0;
    d = 0;
    @(posedge clk);  // Let d_prev settle to 0
    @(posedge clk);
    d = 1;
    @(posedge clk);  // Pulse on first clock after d goes high
    #1;
    check_result("Rising edge after reset generates pulse", 1'b1, q);

    // Print results
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
    #10000;
    $display("ERROR: Simulation timeout!");
    $finish(1);
end

// VCD dump
initial begin
    $dumpfile("posedge_to_pulse_tb.vcd");
    $dumpvars(0, posedge_to_pulse_tb);
end

endmodule
