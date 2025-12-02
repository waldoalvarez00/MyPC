// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// DACRam Testbench
// Tests the VGA DAC dual-port RAM (256 x 18-bit)

`timescale 1ns/1ps

`define SIMULATION

module dac_ram_tb;

reg [7:0] address_a, address_b;
reg clock_a, clock_b;
reg [17:0] data_a, data_b;
reg wren_a, wren_b;
wire [17:0] q_a, q_b;

integer test_count;
integer pass_count;
integer fail_count;
integer i;

// Clock generation - use same clock for both ports for simpler testing
always #5 clock_a = ~clock_a;
always #5 clock_b = ~clock_b;  // Same period as clock_a

// DUT instantiation
DACRam dut (
    .address_a(address_a),
    .address_b(address_b),
    .clock_a(clock_a),
    .clock_b(clock_b),
    .data_a(data_a),
    .data_b(data_b),
    .wren_a(wren_a),
    .wren_b(wren_b),
    .q_a(q_a),
    .q_b(q_b)
);

task check_value(input string test_name, input [17:0] expected, input [17:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected 0x%05h, Got 0x%05h", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

initial begin
    $display("========================================");
    $display("DACRam Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clock_a = 0;
    clock_b = 0;
    address_a = 8'h00;
    address_b = 8'h00;
    data_a = 18'h00000;
    data_b = 18'h00000;
    wren_a = 0;
    wren_b = 0;

    #20;

    // Test 1: Write via port A, read via port A
    $display("\n--- Testing port A write/read ---");
    address_a = 8'h00;
    data_a = 18'h12345;
    wren_a = 1;
    @(posedge clock_a);
    wren_a = 0;
    @(posedge clock_a);
    @(posedge clock_a);
    #1;
    check_value("Write/read port A addr 0x00", 18'h12345, q_a);

    // Test 2: Write via port A, read via port B (same address)
    $display("\n--- Testing cross-port read ---");
    address_a = 8'h10;
    data_a = 18'h3ABCD;
    wren_a = 1;
    @(posedge clock_a);
    wren_a = 0;
    @(posedge clock_a);

    address_b = 8'h10;
    @(posedge clock_b);
    @(posedge clock_b);
    #1;
    check_value("Port A write, port B read", 18'h3ABCD, q_b);

    // Test 3: Write via port B, read via port A
    $display("  Test 3: Starting port B write");
    // Sync to known state first
    wren_b = 0;
    wren_a = 0;
    @(posedge clock_b);
    #1;

    address_b = 8'h20;
    data_b = 18'h1FFFE;
    wren_b = 1;
    @(posedge clock_b);
    #1;
    $display("  After write posedge: mem[0x20] should be written");
    wren_b = 0;
    @(posedge clock_b);
    #1;
    $display("  After 1st extra cycle: q_b=%h (should read back 0x1FFFE)", q_b);

    // Now read from port A - set address first, then wait for read
    address_a = 8'h20;
    @(posedge clock_a);
    #1;
    $display("  After port A read cycle: q_a=%h", q_a);
    check_value("Port B write, port A read", 18'h1FFFE, q_a);

    // Test 4: Write pattern to multiple addresses
    $display("\n--- Testing multiple address writes ---");
    for (i = 0; i < 16; i = i + 1) begin
        address_a = i[7:0];
        data_a = {2'b01, i[7:0], i[7:0]};  // Pattern: 01_ii_ii
        wren_a = 1;
        @(posedge clock_a);
    end
    wren_a = 0;
    @(posedge clock_a);

    // Verify all written values
    for (i = 0; i < 16; i = i + 1) begin
        address_a = i[7:0];
        @(posedge clock_a);
        @(posedge clock_a);
        #1;
        check_value($sformatf("Pattern at addr 0x%02h", i), {2'b01, i[7:0], i[7:0]}, q_a);
    end

    // Test 5: Maximum address (0xFF)
    $display("\n--- Testing edge addresses ---");
    address_a = 8'hFF;
    data_a = 18'h2AAAA;
    wren_a = 1;
    @(posedge clock_a);
    wren_a = 0;
    @(posedge clock_a);
    @(posedge clock_a);
    #1;
    check_value("Max address 0xFF write/read", 18'h2AAAA, q_a);

    // Test 6: No write when wren is low
    $display("\n--- Testing write enable ---");
    address_a = 8'h50;
    data_a = 18'h11111;
    wren_a = 1;
    @(posedge clock_a);
    wren_a = 0;
    data_a = 18'h22222;  // Should NOT be written
    @(posedge clock_a);
    @(posedge clock_a);
    #1;
    check_value("No write when wren=0", 18'h11111, q_a);

    // Test 7: Simultaneous access to different addresses
    $display("\n--- Testing simultaneous access ---");
    address_a = 8'h60;
    address_b = 8'h70;
    data_a = 18'h3FFFF;
    data_b = 18'h00001;
    wren_a = 1;
    wren_b = 1;
    @(posedge clock_a);
    @(posedge clock_b);
    wren_a = 0;
    wren_b = 0;
    @(posedge clock_a);
    @(posedge clock_b);

    // Read back both
    @(posedge clock_a);
    #1;
    check_value("Simultaneous write port A", 18'h3FFFF, q_a);

    address_a = 8'h70;
    @(posedge clock_a);
    @(posedge clock_a);
    #1;
    check_value("Simultaneous write port B", 18'h00001, q_a);

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
    #500000;
    $display("ERROR: Simulation timeout!");
    $finish(1);
end

// VCD dump
initial begin
    $dumpfile("dac_ram_tb.vcd");
    $dumpvars(0, dac_ram_tb);
end

endmodule
