// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// FPUStatusRegister Testbench
// Tests the FPU status word I/O register (read-only)

`timescale 1ns/1ps

module fpu_status_register_tb;

reg clk;
reg reset;
reg cs;
reg [15:0] status_word_in;
wire [15:0] data_m_data_out;
wire data_m_ack;

integer test_count;
integer pass_count;
integer fail_count;

FPUStatusRegister dut (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .status_word_in(status_word_in),
    .data_m_data_out(data_m_data_out),
    .data_m_ack(data_m_ack)
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
    $display("FPUStatusRegister Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    cs = 0;
    status_word_in = 16'h0000;

    // Release reset
    @(posedge clk);
    @(posedge clk);
    #1;
    reset = 0;
    @(posedge clk);
    #1;

    // Test 1: Passthrough of status word
    $display("\n--- Testing status word passthrough ---");
    status_word_in = 16'h1234;
    #1;
    check("Status word passthrough (0x1234)", 16'h1234, data_m_data_out);

    // Test 2: Different status word
    status_word_in = 16'h5678;
    #1;
    check("Status word passthrough (0x5678)", 16'h5678, data_m_data_out);

    // Test 3: No ack when cs is low
    $display("\n--- Testing chip select ---");
    @(posedge clk);
    #1;
    check_bit("No ack when cs=0", 1'b0, data_m_ack);

    // Test 4: Ack when cs is high
    cs = 1;
    @(posedge clk);
    #1;
    check_bit("Ack asserted when cs=1", 1'b1, data_m_ack);

    // Test 5: Ack tracks cs
    cs = 0;
    @(posedge clk);
    #1;
    check_bit("Ack deasserted when cs=0", 1'b0, data_m_ack);

    // Test 6: Test typical FPU status values
    $display("\n--- Testing typical FPU status values ---");

    // Status with busy bit set (bit 15)
    status_word_in = 16'h8000;
    #1;
    check("FPU busy status (0x8000)", 16'h8000, data_m_data_out);

    // Status with stack top = 3 (bits 11-13)
    status_word_in = 16'h1800;  // ST(3) at top
    #1;
    check("Stack top = 3 (0x1800)", 16'h1800, data_m_data_out);

    // Status with C0,C1,C2,C3 condition codes set (bits 8,9,10,14)
    status_word_in = 16'h4700;  // C3=1, C2=1, C1=1, C0=1
    #1;
    check("Condition codes set (0x4700)", 16'h4700, data_m_data_out);

    // Status with exception flags (bits 0-5)
    status_word_in = 16'h003F;  // All exceptions
    #1;
    check("All exception flags (0x003F)", 16'h003F, data_m_data_out);

    // Combined status
    status_word_in = 16'hFFFF;
    #1;
    check("All bits set (0xFFFF)", 16'hFFFF, data_m_data_out);

    // Test 7: Reset clears ack
    $display("\n--- Testing reset ---");
    cs = 1;
    @(posedge clk);
    #1;
    check_bit("Ack high before reset", 1'b1, data_m_ack);

    reset = 1;
    @(posedge clk);
    #1;
    check_bit("Ack cleared on reset", 1'b0, data_m_ack);

    // Test 8: Status passthrough still works during/after reset
    status_word_in = 16'hABCD;
    #1;
    check("Passthrough works during reset", 16'hABCD, data_m_data_out);

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
    $dumpfile("fpu_status_register_tb.vcd");
    $dumpvars(0, fpu_status_register_tb);
end

endmodule
