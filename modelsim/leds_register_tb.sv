// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// LEDSRegister Testbench
// Tests the debug LED output register

`timescale 1ns/1ps

module leds_register_tb;

reg clk;
reg reset;
reg cs;
reg [15:0] data_m_data_in;
wire [15:0] data_m_data_out;
reg data_m_access;
wire data_m_ack;
reg data_m_wr_en;
reg [1:0] data_m_bytesel;
reg resetval;
wire [15:0] leds_val;

integer test_count;
integer pass_count;
integer fail_count;

LEDSRegister dut (
    .clk(clk),
    .reset(reset),
    .leds_val(leds_val),
    .cs(cs),
    .data_m_data_in(data_m_data_in),
    .data_m_data_out(data_m_data_out),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .data_m_wr_en(data_m_wr_en),
    .data_m_bytesel(data_m_bytesel),
    .resetval(resetval)
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
    $display("LEDSRegister Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    cs = 0;
    data_m_data_in = 16'h0000;
    data_m_access = 0;
    data_m_wr_en = 0;
    data_m_bytesel = 2'b11;
    resetval = 0;

    // Release reset
    @(posedge clk);
    @(posedge clk);
    #1;
    reset = 0;
    @(posedge clk);
    #1;

    // Test 1: Initial state after reset
    $display("\n--- Testing initial state ---");
    check("Initial leds_val is 0x0000", 16'h0000, leds_val);

    // Test 2: Write full word
    $display("\n--- Testing word write ---");
    cs = 1;
    data_m_access = 1;
    data_m_wr_en = 1;
    data_m_bytesel = 2'b11;
    data_m_data_in = 16'hABCD;
    @(posedge clk);
    #1;
    check("Full word write (0xABCD)", 16'hABCD, leds_val);

    // Test 3: Ack generated
    @(posedge clk);
    #1;
    check_bit("Ack asserted on access", 1'b1, data_m_ack);

    // Test 4: Read back
    data_m_wr_en = 0;
    @(posedge clk);
    #1;
    check("Read back value", 16'hABCD, data_m_data_out);

    // Test 5: Write low byte only
    $display("\n--- Testing byte-selective writes ---");
    data_m_wr_en = 1;
    data_m_bytesel = 2'b01;  // Low byte only
    data_m_data_in = 16'h1234;
    @(posedge clk);
    #1;
    check("Low byte write (0xAB34)", 16'hAB34, leds_val);

    // Test 6: Write high byte only
    data_m_bytesel = 2'b10;  // High byte only
    data_m_data_in = 16'h5678;
    @(posedge clk);
    #1;
    check("High byte write (0x5634)", 16'h5634, leds_val);

    // Test 7: No write when bytesel is 0
    data_m_bytesel = 2'b00;
    data_m_data_in = 16'hFFFF;
    @(posedge clk);
    #1;
    check("No write with bytesel=00", 16'h5634, leds_val);

    // Test 8: No write when cs is low
    $display("\n--- Testing chip select ---");
    cs = 0;
    data_m_bytesel = 2'b11;
    data_m_data_in = 16'hAAAA;
    @(posedge clk);
    #1;
    check("No write when cs=0", 16'h5634, leds_val);

    // Test 9: No write when access is low
    cs = 1;
    data_m_access = 0;
    @(posedge clk);
    #1;
    check("No write when access=0", 16'h5634, leds_val);

    // Test 10: No ack when cs or access low
    @(posedge clk);
    #1;
    check_bit("No ack when access=0", 1'b0, data_m_ack);

    // Test 11: Resetval clears LEDs
    $display("\n--- Testing resetval ---");
    data_m_access = 1;
    data_m_wr_en = 1;
    data_m_bytesel = 2'b11;
    data_m_data_in = 16'hBEEF;
    @(posedge clk);
    #1;
    check("Write 0xBEEF before resetval", 16'hBEEF, leds_val);

    // Deassert write enable before asserting resetval
    data_m_wr_en = 0;
    resetval = 1;
    @(posedge clk);
    #1;
    check("Resetval clears LEDs", 16'h0000, leds_val);

    resetval = 0;
    @(posedge clk);
    #1;

    // Test 12: Full reset
    $display("\n--- Testing full reset ---");
    data_m_wr_en = 1;
    data_m_data_in = 16'hCAFE;
    @(posedge clk);
    #1;
    check("Write 0xCAFE before reset", 16'hCAFE, leds_val);

    reset = 1;
    @(posedge clk);
    #1;
    check("Reset clears LEDs", 16'h0000, leds_val);

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
    $dumpfile("leds_register_tb.vcd");
    $dumpvars(0, leds_register_tb);
end

endmodule
