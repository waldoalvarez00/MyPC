// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// AckExtender Testbench
// Tests the acknowledgement signal extender module

`timescale 1ns/1ps

module ack_extender_tb;

reg clk;
reg rst_n;  // Note: Active HIGH reset despite name
reg ack_in;
wire ack_out;

integer test_count;
integer pass_count;
integer fail_count;

// Default parameter: EXTEND_CYCLES = 3
AckExtender #(.EXTEND_CYCLES(3)) dut (
    .clk(clk),
    .rst_n(rst_n),
    .ack_in(ack_in),
    .ack_out(ack_out)
);

// Clock generation: 10ns period
always #5 clk = ~clk;

task check(input string test_name, input expected, input actual);
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
    $display("AckExtender Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    rst_n = 1;  // Assert reset (active HIGH)
    ack_in = 0;

    // Wait for reset
    @(posedge clk);
    @(posedge clk);
    #1;

    // Release reset
    rst_n = 0;
    @(posedge clk);
    #1;

    // Test 1: Initial state - no ack
    $display("\n--- Testing initial state ---");
    check("Initial ack_out should be 0", 1'b0, ack_out);

    // Test 2: Assert ack_in - ack_out should go high immediately
    $display("\n--- Testing ack extension ---");
    ack_in = 1;
    #1;
    check("ack_out high immediately when ack_in asserted", 1'b1, ack_out);

    // Test 3: After clock edge, counter starts
    @(posedge clk);
    #1;
    check("ack_out stays high after first clock", 1'b1, ack_out);

    // Test 4: Deassert ack_in - ack_out should stay high (extension)
    // Counter was loaded with 3 when ack_in was high
    // Now ack_in=0, counter decrements: 3->2
    ack_in = 0;
    @(posedge clk);
    #1;
    check("ack_out stays high after ack_in deasserted (counter=2)", 1'b1, ack_out);

    // Test 5: Continue counting down (counter 2->1)
    @(posedge clk);
    #1;
    check("ack_out stays high (counter=1)", 1'b1, ack_out);

    // Test 6: Counter reaches 0, ack_out goes low
    @(posedge clk);
    #1;
    check("ack_out goes low when counter reaches 0", 1'b0, ack_out);

    // Test 8: Re-trigger ack during extension (reset counter)
    $display("\n--- Testing re-trigger during extension ---");
    ack_in = 1;
    @(posedge clk);
    #1;
    check("ack_out high on re-trigger", 1'b1, ack_out);

    ack_in = 0;
    @(posedge clk);
    #1;

    // Re-trigger before extension completes
    ack_in = 1;
    @(posedge clk);
    #1;
    check("ack_out still high on re-trigger during extension", 1'b1, ack_out);

    ack_in = 0;
    // Counter was reloaded with 3, now counts down: 3->2->1->0
    @(posedge clk); #1;  // counter = 2
    check("ack_out high 1 cycle after re-trigger (counter=2)", 1'b1, ack_out);
    @(posedge clk); #1;  // counter = 1
    check("ack_out high 2 cycles after re-trigger (counter=1)", 1'b1, ack_out);
    @(posedge clk); #1;  // counter = 0
    check("ack_out low 3 cycles after re-trigger (counter=0)", 1'b0, ack_out);

    // Test 9: Reset clears state
    $display("\n--- Testing reset ---");
    ack_in = 1;
    @(posedge clk);
    #1;
    ack_in = 0;

    rst_n = 1;  // Assert reset
    @(posedge clk);
    #1;
    check("ack_out low after reset (counter cleared)", 1'b0, ack_out);

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
    $dumpfile("ack_extender_tb.vcd");
    $dumpvars(0, ack_extender_tb);
end

endmodule
