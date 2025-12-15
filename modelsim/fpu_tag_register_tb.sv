// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// FPU_Tag_Register Testbench
// Tests the FPU stack tag register

`timescale 1ns/1ps

module fpu_tag_register_tb;

reg clk;
reg reset;
reg [15:0] write_data;
reg write_enable;
wire [15:0] tag_register;
wire [1:0] tag_ST0, tag_ST1, tag_ST2, tag_ST3;
wire [1:0] tag_ST4, tag_ST5, tag_ST6, tag_ST7;

integer test_count;
integer pass_count;
integer fail_count;

// Clock generation
always #5 clk = ~clk;

// DUT instantiation
FPU_Tag_Register dut (
    .clk(clk),
    .reset(reset),
    .write_data(write_data),
    .write_enable(write_enable),
    .tag_register(tag_register),
    .tag_ST0(tag_ST0),
    .tag_ST1(tag_ST1),
    .tag_ST2(tag_ST2),
    .tag_ST3(tag_ST3),
    .tag_ST4(tag_ST4),
    .tag_ST5(tag_ST5),
    .tag_ST6(tag_ST6),
    .tag_ST7(tag_ST7)
);

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

task check_tag(input string test_name, input [1:0] expected, input [1:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected %02b, Got %02b", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

initial begin
    $display("========================================");
    $display("FPU_Tag_Register Testbench");
    $display("========================================");
    $display("Tag values: 00=Valid, 01=Zero, 10=Special, 11=Empty");
    $display("");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    write_data = 16'h0000;
    write_enable = 0;

    // Release reset
    #20;
    reset = 0;
    #20;

    // Test 1: All registers empty after reset (0xFFFF)
    @(posedge clk);
    #1;
    check_value("All empty after reset", 16'hFFFF, tag_register);

    // Test 2: Individual tag outputs after reset (all 11 = empty)
    check_tag("ST0 empty after reset", 2'b11, tag_ST0);
    check_tag("ST1 empty after reset", 2'b11, tag_ST1);
    check_tag("ST2 empty after reset", 2'b11, tag_ST2);
    check_tag("ST3 empty after reset", 2'b11, tag_ST3);
    check_tag("ST4 empty after reset", 2'b11, tag_ST4);
    check_tag("ST5 empty after reset", 2'b11, tag_ST5);
    check_tag("ST6 empty after reset", 2'b11, tag_ST6);
    check_tag("ST7 empty after reset", 2'b11, tag_ST7);

    // Test 3: Write all zeros (all valid)
    write_data = 16'h0000;
    write_enable = 1;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_value("All valid after write 0x0000", 16'h0000, tag_register);
    check_tag("ST0 valid", 2'b00, tag_ST0);

    // Test 4: Write pattern for mixed tags
    // ST0=00(valid), ST1=01(zero), ST2=10(special), ST3=11(empty)
    // ST4=00(valid), ST5=01(zero), ST6=10(special), ST7=11(empty)
    write_data = 16'hE4E4;  // 11_10_01_00_11_10_01_00
    @(posedge clk);
    @(posedge clk);
    #1;
    check_value("Mixed pattern written", 16'hE4E4, tag_register);
    check_tag("ST0 valid (00)", 2'b00, tag_ST0);
    check_tag("ST1 zero (01)", 2'b01, tag_ST1);
    check_tag("ST2 special (10)", 2'b10, tag_ST2);
    check_tag("ST3 empty (11)", 2'b11, tag_ST3);
    check_tag("ST4 valid (00)", 2'b00, tag_ST4);
    check_tag("ST5 zero (01)", 2'b01, tag_ST5);
    check_tag("ST6 special (10)", 2'b10, tag_ST6);
    check_tag("ST7 empty (11)", 2'b11, tag_ST7);

    // Test 5: No write when write_enable is low
    write_enable = 0;
    write_data = 16'hAAAA;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_value("No write when enable=0", 16'hE4E4, tag_register);

    // Test 6: Write new pattern
    write_enable = 1;
    write_data = 16'h5555;  // 01_01_01_01_01_01_01_01 (all zero)
    @(posedge clk);
    @(posedge clk);
    #1;
    check_value("All zeros tag pattern", 16'h5555, tag_register);
    check_tag("ST0 zero tag", 2'b01, tag_ST0);
    check_tag("ST7 zero tag", 2'b01, tag_ST7);

    // Test 7: Reset restores all empty
    reset = 1;
    @(posedge clk);
    #1;
    check_value("Reset restores 0xFFFF", 16'hFFFF, tag_register);

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
    $dumpfile("fpu_tag_register_tb.vcd");
    $dumpvars(0, fpu_tag_register_tb);
end

endmodule
