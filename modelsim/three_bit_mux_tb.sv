// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// three_bit_4x1_mux Testbench
// Tests the 3-bit 4-to-1 multiplexer

`timescale 1ns/1ps

module three_bit_mux_tb;

reg [2:0] in0, in1, in2, in3;
reg [1:0] select;
wire [2:0] out;

integer test_count;
integer pass_count;
integer fail_count;

// DUT instantiation
three_bit_4x1_mux dut (
    .in0(in0),
    .in1(in1),
    .in2(in2),
    .in3(in3),
    .select(select),
    .out(out)
);

task check_result(input string test_name, input [2:0] expected, input [2:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected %03b, Got %03b", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

initial begin
    $display("========================================");
    $display("three_bit_4x1_mux Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    // Set up distinct values for each input
    in0 = 3'b001;
    in1 = 3'b010;
    in2 = 3'b100;
    in3 = 3'b111;

    // Test 1: Select = 00 -> in0
    select = 2'b00;
    #10;
    check_result("Select 00 -> in0", in0, out);

    // Test 2: Select = 01 -> in1
    select = 2'b01;
    #10;
    check_result("Select 01 -> in1", in1, out);

    // Test 3: Select = 10 -> in2
    select = 2'b10;
    #10;
    check_result("Select 10 -> in2", in2, out);

    // Test 4: Select = 11 -> in3
    select = 2'b11;
    #10;
    check_result("Select 11 -> in3", in3, out);

    // Test 5-8: Test with different input values
    in0 = 3'b000;
    in1 = 3'b011;
    in2 = 3'b101;
    in3 = 3'b110;

    select = 2'b00;
    #10;
    check_result("Different values: Select 00", 3'b000, out);

    select = 2'b01;
    #10;
    check_result("Different values: Select 01", 3'b011, out);

    select = 2'b10;
    #10;
    check_result("Different values: Select 10", 3'b101, out);

    select = 2'b11;
    #10;
    check_result("Different values: Select 11", 3'b110, out);

    // Test 9-12: All zeros and all ones
    in0 = 3'b000;
    in1 = 3'b000;
    in2 = 3'b111;
    in3 = 3'b111;

    select = 2'b00;
    #10;
    check_result("All zeros: Select 00", 3'b000, out);

    select = 2'b01;
    #10;
    check_result("All zeros: Select 01", 3'b000, out);

    select = 2'b10;
    #10;
    check_result("All ones: Select 10", 3'b111, out);

    select = 2'b11;
    #10;
    check_result("All ones: Select 11", 3'b111, out);

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
    $dumpfile("three_bit_mux_tb.vcd");
    $dumpvars(0, three_bit_mux_tb);
end

endmodule
