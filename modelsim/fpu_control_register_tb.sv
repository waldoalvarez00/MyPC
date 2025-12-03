// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// FPUControlRegister Testbench
// Tests the FPU control word I/O register

`timescale 1ns/1ps

module fpu_control_register_tb;

reg clk;
reg reset;
reg cs;
reg [15:0] data_m_data_in;
reg data_m_wr_en;
wire data_m_ack;
wire [15:0] control_word_out;
wire control_write;

integer test_count;
integer pass_count;
integer fail_count;

FPUControlRegister dut (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .data_m_data_in(data_m_data_in),
    .data_m_wr_en(data_m_wr_en),
    .data_m_ack(data_m_ack),
    .control_word_out(control_word_out),
    .control_write(control_write)
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
    $display("FPUControlRegister Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    cs = 0;
    data_m_data_in = 16'h0000;
    data_m_wr_en = 0;

    // Release reset
    @(posedge clk);
    @(posedge clk);
    #1;
    reset = 0;
    @(posedge clk);
    #1;

    // Test 1: Default control word (0x037F after reset)
    $display("\n--- Testing default value ---");
    check("Default control word is 0x037F", 16'h037F, control_word_out);

    // Test 2: No ack when cs is low
    $display("\n--- Testing chip select ---");
    @(posedge clk);
    #1;
    check_bit("No ack when cs=0", 1'b0, data_m_ack);

    // Test 3: Ack when cs is high
    cs = 1;
    @(posedge clk);
    #1;
    check_bit("Ack asserted when cs=1", 1'b1, data_m_ack);

    // Test 4: Write new control word
    $display("\n--- Testing write operation ---");
    data_m_data_in = 16'h1234;
    data_m_wr_en = 1;
    @(posedge clk);
    #1;
    check("Control word updated to 0x1234", 16'h1234, control_word_out);
    check_bit("control_write pulse on write", 1'b1, control_write);

    // Test 5: control_write clears after one cycle
    data_m_wr_en = 0;
    @(posedge clk);
    #1;
    check_bit("control_write cleared after one cycle", 1'b0, control_write);

    // Test 6: Read back (control word unchanged)
    check("Control word still 0x1234 after read", 16'h1234, control_word_out);

    // Test 7: Write another value
    $display("\n--- Testing multiple writes ---");
    data_m_data_in = 16'h5678;
    data_m_wr_en = 1;
    @(posedge clk);
    #1;
    check("Control word updated to 0x5678", 16'h5678, control_word_out);

    // Test 8: Write with typical FPU control settings
    // Round to nearest, 64-bit precision, all exceptions masked
    data_m_data_in = 16'h037F;
    @(posedge clk);
    #1;
    check("Control word set to standard 0x037F", 16'h037F, control_word_out);

    // Test 9: No write when wr_en is low
    cs = 1;
    data_m_wr_en = 0;
    data_m_data_in = 16'hFFFF;
    @(posedge clk);
    #1;
    check("Control word unchanged when wr_en=0", 16'h037F, control_word_out);

    // Test 10: No write when cs is low
    cs = 0;
    data_m_wr_en = 1;
    data_m_data_in = 16'hAAAA;
    @(posedge clk);
    #1;
    check("Control word unchanged when cs=0", 16'h037F, control_word_out);

    // Test 11: Reset restores default
    $display("\n--- Testing reset ---");
    cs = 1;
    data_m_wr_en = 1;
    data_m_data_in = 16'hBEEF;
    @(posedge clk);
    #1;
    check("Control word set to 0xBEEF before reset", 16'hBEEF, control_word_out);

    reset = 1;
    @(posedge clk);
    #1;
    check("Control word restored to 0x037F after reset", 16'h037F, control_word_out);
    check_bit("Ack cleared on reset", 1'b0, data_m_ack);
    check_bit("control_write cleared on reset", 1'b0, control_write);

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
    $dumpfile("fpu_control_register_tb.vcd");
    $dumpvars(0, fpu_control_register_tb);
end

endmodule
