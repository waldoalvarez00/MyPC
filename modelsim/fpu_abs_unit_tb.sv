// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// FPU_ABS_Unit Testbench
// Tests the 80-bit floating-point absolute value unit

`timescale 1ns/1ps

module fpu_abs_unit_tb;

reg [79:0] in;
wire [79:0] out;

integer test_count;
integer pass_count;
integer fail_count;

// DUT instantiation
FPU_ABS_Unit dut (
    .in(in),
    .out(out)
);

task check_result(input string test_name, input [79:0] expected, input [79:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s", test_count, test_name);
        $display("       Expected: %020h", expected);
        $display("       Got:      %020h", actual);
        fail_count = fail_count + 1;
    end
end
endtask

initial begin
    $display("========================================");
    $display("FPU_ABS_Unit Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    // Test 1: Positive number stays positive (sign bit already 0)
    in = 80'h3FFF_8000_0000_0000_0000;  // +1.0 in 80-bit extended
    #10;
    check_result("Positive +1.0 unchanged", 80'h3FFF_8000_0000_0000_0000, out);

    // Test 2: Negative number becomes positive (clear sign bit)
    in = 80'hBFFF_8000_0000_0000_0000;  // -1.0 in 80-bit extended
    #10;
    check_result("Negative -1.0 -> +1.0", 80'h3FFF_8000_0000_0000_0000, out);

    // Test 3: Positive zero stays positive zero
    in = 80'h0000_0000_0000_0000_0000;  // +0.0
    #10;
    check_result("Positive zero unchanged", 80'h0000_0000_0000_0000_0000, out);

    // Test 4: Negative zero becomes positive zero
    in = 80'h8000_0000_0000_0000_0000;  // -0.0
    #10;
    check_result("Negative zero -> positive zero", 80'h0000_0000_0000_0000_0000, out);

    // Test 5: Positive infinity unchanged
    in = 80'h7FFF_8000_0000_0000_0000;  // +Infinity
    #10;
    check_result("Positive infinity unchanged", 80'h7FFF_8000_0000_0000_0000, out);

    // Test 6: Negative infinity becomes positive infinity
    in = 80'hFFFF_8000_0000_0000_0000;  // -Infinity
    #10;
    check_result("Negative infinity -> positive infinity", 80'h7FFF_8000_0000_0000_0000, out);

    // Test 7: Positive NaN unchanged
    in = 80'h7FFF_C000_0000_0000_0000;  // +NaN (quiet)
    #10;
    check_result("Positive NaN unchanged", 80'h7FFF_C000_0000_0000_0000, out);

    // Test 8: Negative NaN becomes positive NaN
    in = 80'hFFFF_C000_0000_0000_0000;  // -NaN (quiet)
    #10;
    check_result("Negative NaN -> positive NaN", 80'h7FFF_C000_0000_0000_0000, out);

    // Test 9: Large positive number unchanged
    in = 80'h4000_A000_0000_0000_0000;  // +2.5
    #10;
    check_result("Large positive unchanged", 80'h4000_A000_0000_0000_0000, out);

    // Test 10: Large negative number becomes positive
    in = 80'hC000_A000_0000_0000_0000;  // -2.5
    #10;
    check_result("Large negative -> positive", 80'h4000_A000_0000_0000_0000, out);

    // Test 11: Small positive denormal unchanged
    in = 80'h0000_0000_0000_0000_0001;  // Small denormal
    #10;
    check_result("Small denormal unchanged", 80'h0000_0000_0000_0000_0001, out);

    // Test 12: Small negative denormal becomes positive
    in = 80'h8000_0000_0000_0000_0001;  // Small negative denormal
    #10;
    check_result("Small negative denormal -> positive", 80'h0000_0000_0000_0000_0001, out);

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
    $dumpfile("fpu_abs_unit_tb.vcd");
    $dumpvars(0, fpu_abs_unit_tb);
end

endmodule
