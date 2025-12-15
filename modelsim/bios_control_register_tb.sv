// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// BIOSControlRegister Testbench
// Tests the BIOS enable/disable control register

`timescale 1ns/1ps

module bios_control_register_tb;

reg clk;
reg reset;
reg cs;
wire [15:0] data_m_data_out;
reg [15:0] data_m_data_in;
reg data_m_wr_en;
reg data_m_access;
wire data_m_ack;
wire bios_enabled;

integer test_count;
integer pass_count;
integer fail_count;

// Clock generation
always #5 clk = ~clk;

// DUT instantiation
BIOSControlRegister dut (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .data_m_data_out(data_m_data_out),
    .data_m_data_in(data_m_data_in),
    .data_m_wr_en(data_m_wr_en),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .bios_enabled(bios_enabled)
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

task check_value(input string test_name, input [15:0] expected, input [15:0] actual);
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
    $display("BIOSControlRegister Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    cs = 0;
    data_m_data_in = 16'h0000;
    data_m_wr_en = 0;
    data_m_access = 0;

    // Release reset
    #20;
    reset = 0;
    #20;

    // Test 1: BIOS enabled after reset
    @(posedge clk);
    #1;
    check_result("BIOS enabled after reset", 1'b1, bios_enabled);

    // Test 2: No ACK when not selected
    @(posedge clk);
    #1;
    check_result("No ACK when cs=0", 1'b0, data_m_ack);

    // Test 3: Read BIOS status (should be 1)
    cs = 1;
    data_m_access = 1;
    data_m_wr_en = 0;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("ACK on read access", 1'b1, data_m_ack);
    check_value("Read returns bios_enabled=1", 16'h0001, data_m_data_out);

    // Test 4: Write 0 to disable BIOS
    data_m_wr_en = 1;
    data_m_data_in = 16'h0000;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("BIOS disabled after write 0", 1'b0, bios_enabled);

    // Test 5: Read back disabled status
    data_m_wr_en = 0;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_value("Read returns bios_enabled=0", 16'h0000, data_m_data_out);

    // Test 6: Write 1 to re-enable BIOS
    data_m_wr_en = 1;
    data_m_data_in = 16'h0001;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("BIOS re-enabled after write 1", 1'b1, bios_enabled);

    // Test 7: Write with upper bits set (only bit 0 matters)
    data_m_data_in = 16'hFFFE;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("Only bit 0 used (FFFEh -> disabled)", 1'b0, bios_enabled);

    // Test 8: No write when cs is low
    cs = 0;
    data_m_data_in = 16'h0001;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("No write when cs=0", 1'b0, bios_enabled);

    // Test 9: No write when access is low
    cs = 1;
    data_m_access = 0;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("No write when access=0", 1'b0, bios_enabled);

    // Test 10: Reset re-enables BIOS
    reset = 1;
    @(posedge clk);
    #1;
    check_result("Reset re-enables BIOS", 1'b1, bios_enabled);

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
    #50000;
    $display("ERROR: Simulation timeout!");
    $finish(1);
end

// VCD dump
initial begin
    $dumpfile("bios_control_register_tb.vcd");
    $dumpvars(0, bios_control_register_tb);
end

endmodule
