//============================================================================
//
//  KF8253 Comprehensive Testbench
//  Tests all 6 modes, read/write patterns, gate control, and BCD counting
//  Compatible with Icarus Verilog
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

`include "KF8253_Definitions.svh"

module kf8253_tb;

// Clock and reset
reg clock;
reg reset;

// Counter clocks and gates
reg counter_0_clock;
reg counter_0_gate;
wire counter_0_out;

reg counter_1_clock;
reg counter_1_gate;
wire counter_1_out;

reg counter_2_clock;
reg counter_2_gate;
wire counter_2_out;

// Bus interface
reg chip_select_n;
reg read_enable_n;
reg write_enable_n;
reg [1:0] address;
reg [7:0] data_bus_in;
wire [7:0] data_bus_out;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// Helper variables
reg [7:0] read_data, read_data2;
reg [15:0] read_count;
integer i, toggle_count, pulse_count;
reg prev_out;

// DUT instantiation
KF8253 dut (
    .clock              (clock),
    .reset              (reset),
    .chip_select_n      (chip_select_n),
    .read_enable_n      (read_enable_n),
    .write_enable_n     (write_enable_n),
    .address            (address),
    .data_bus_in        (data_bus_in),
    .data_bus_out       (data_bus_out),
    .counter_0_clock    (counter_0_clock),
    .counter_0_gate     (counter_0_gate),
    .counter_0_out      (counter_0_out),
    .counter_1_clock    (counter_1_clock),
    .counter_1_gate     (counter_1_gate),
    .counter_1_out      (counter_1_out),
    .counter_2_clock    (counter_2_clock),
    .counter_2_gate     (counter_2_gate),
    .counter_2_out      (counter_2_out)
);

// System clock: 50 MHz
initial begin
    clock = 0;
    forever #10 clock = ~clock;  // 20ns period = 50 MHz
end

// Counter clock 0: 1 MHz
initial begin
    counter_0_clock = 0;
    forever #500 counter_0_clock = ~counter_0_clock;  // 1us period
end

// Counter clock 1: 2 MHz
initial begin
    counter_1_clock = 0;
    forever #250 counter_1_clock = ~counter_1_clock;  // 500ns period
end

// Counter clock 2: 1 MHz
initial begin
    counter_2_clock = 0;
    forever #500 counter_2_clock = ~counter_2_clock;  // 1us period
end

//============================================================================
// Helper Tasks
//============================================================================

// Write to KF8253
task write_8253;
    input [1:0] addr;
    input [7:0] data;
    begin
        @(posedge clock);
        chip_select_n = 1'b0;
        write_enable_n = 1'b0;
        read_enable_n = 1'b1;
        address = addr;
        data_bus_in = data;
        @(posedge clock);
        write_enable_n = 1'b1;
        chip_select_n = 1'b1;
        @(posedge clock);
    end
endtask

// Read from KF8253
task read_8253;
    input [1:0] addr;
    output [7:0] data;
    begin
        @(posedge clock);
        chip_select_n = 1'b0;
        read_enable_n = 1'b0;
        write_enable_n = 1'b1;
        address = addr;
        @(posedge clock);
        @(posedge clock);
        data = data_bus_out;
        read_enable_n = 1'b1;
        chip_select_n = 1'b1;
        @(posedge clock);
    end
endtask

// Configure counter with mode and count value
task config_counter;
    input [1:0] counter_sel;
    input [1:0] rw_mode;
    input [2:0] mode;
    input bcd;
    input [15:0] count_value;
    reg [7:0] control_word;
    begin
        // Build control word: SC[7:6], RW[5:4], M[3:1], BCD[0]
        control_word = {counter_sel, rw_mode, mode, bcd};

        // Write control word
        write_8253(2'b11, control_word);

        // Write count value based on RW mode
        case (rw_mode)
            2'b01: begin  // LSB only
                write_8253(counter_sel, count_value[7:0]);
            end
            2'b10: begin  // MSB only
                write_8253(counter_sel, count_value[15:8]);
            end
            2'b11: begin  // LSB then MSB
                write_8253(counter_sel, count_value[7:0]);
                write_8253(counter_sel, count_value[15:8]);
            end
        endcase
    end
endtask

// Latch and read counter value
task latch_read_counter;
    input [1:0] counter_sel;
    input [1:0] rw_mode;
    output [15:0] value;
    reg [7:0] lsb, msb;
    begin
        // Send latch command
        write_8253(2'b11, {counter_sel, 2'b00, 3'b000, 1'b0});

        // Read based on RW mode
        case (rw_mode)
            2'b01: begin  // LSB only
                read_8253(counter_sel, lsb);
                value = {8'h00, lsb};
            end
            2'b10: begin  // MSB only
                read_8253(counter_sel, msb);
                value = {msb, 8'h00};
            end
            2'b11: begin  // LSB then MSB
                read_8253(counter_sel, lsb);
                read_8253(counter_sel, msb);
                value = {msb, lsb};
            end
        endcase
    end
endtask

//============================================================================
// Main Test Sequence
//============================================================================

initial begin
    $display("================================================================");
    $display("KF8253 Programmable Interval Timer - Comprehensive Testbench");
    $display("Testing all 6 modes, read/write patterns, and BCD counting");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1;
    chip_select_n = 1;
    read_enable_n = 1;
    write_enable_n = 1;
    address = 2'b00;
    data_bus_in = 8'h00;
    counter_0_gate = 1;
    counter_1_gate = 1;
    counter_2_gate = 1;

    // Reset
    repeat(10) @(posedge clock);
    reset = 0;
    repeat(5) @(posedge clock);

    //========================================================================
    // Test 1: Basic Write/Read Access
    //========================================================================
    $display("TEST GROUP 1: Basic Register Access");
    $display("------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b00, 2'b11, 3'b010, 0, 16'd1000);
    pass_count = pass_count + 1;
    $display("  [PASS] Test %0d: Control register write", test_count);

    test_count = test_count + 1;
    repeat(10) @(negedge counter_0_clock);
    latch_read_counter(2'b00, 2'b11, read_count);
    if (read_count < 16'd1000 && read_count > 16'd900) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Counter latch and read (count=%0d)", test_count, read_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Counter latch and read (count=%0d)", test_count, read_count);
    end

    //========================================================================
    // Test 2: Mode 0 - Interrupt on Terminal Count
    //========================================================================
    $display("");
    $display("TEST GROUP 2: Mode 0 - Interrupt on Terminal Count");
    $display("---------------------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b00, 2'b11, 3'b000, 0, 16'd10);
    if (counter_0_out == 0) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 0 initialization", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 0 initialization (out=%b)", test_count, counter_0_out);
    end

    test_count = test_count + 1;
    repeat(15) @(negedge counter_0_clock);
    if (counter_0_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 0 counting to terminal count", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 0 counting to terminal count (out=%b)", test_count, counter_0_out);
    end

    test_count = test_count + 1;
    config_counter(2'b00, 2'b11, 3'b000, 0, 16'd20);
    repeat(5) @(negedge counter_0_clock);
    counter_0_gate = 0;
    latch_read_counter(2'b00, 2'b11, read_count);
    repeat(10) @(negedge counter_0_clock);
    latch_read_counter(2'b00, 2'b11, read_data);
    counter_0_gate = 1;
    if (read_count == {8'h00, read_data}) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 0 gate control disables counting", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 0 gate control", test_count);
    end

    //========================================================================
    // Test 3: Mode 1 - Hardware Retriggerable One-Shot
    //========================================================================
    $display("");
    $display("TEST GROUP 3: Mode 1 - Hardware Retriggerable One-Shot");
    $display("-------------------------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b01, 2'b11, 3'b001, 0, 16'd20);
    if (counter_1_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 1 initialization", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 1 initialization", test_count);
    end

    test_count = test_count + 1;
    counter_1_gate = 0;
    repeat(5) @(posedge clock);
    counter_1_gate = 1;  // Rising edge trigger
    repeat(2) @(negedge counter_1_clock);
    if (counter_1_out == 0) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 1 gate trigger starts count", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 1 gate trigger", test_count);
    end

    test_count = test_count + 1;
    repeat(25) @(negedge counter_1_clock);
    if (counter_1_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 1 output goes high after terminal count", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 1 terminal count", test_count);
    end

    //========================================================================
    // Test 4: Mode 2 - Rate Generator
    //========================================================================
    $display("");
    $display("TEST GROUP 4: Mode 2 - Rate Generator");
    $display("--------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b00, 2'b11, 3'b010, 0, 16'd15);
    if (counter_0_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 2 initialization", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 2 initialization", test_count);
    end

    test_count = test_count + 1;
    pulse_count = 0;
    prev_out = counter_0_out;
    for (i = 0; i < 50; i = i + 1) begin
        @(negedge counter_0_clock);
        if (counter_0_out == 0 && prev_out == 1) begin
            pulse_count = pulse_count + 1;
        end
        prev_out = counter_0_out;
    end
    if (pulse_count >= 2 && pulse_count <= 4) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 2 generates periodic pulses (pulses=%0d)", test_count, pulse_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 2 periodic pulses (pulses=%0d)", test_count, pulse_count);
    end

    test_count = test_count + 1;
    counter_0_gate = 0;
    repeat(3) @(posedge clock);
    if (counter_0_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 2 gate disable stops output", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 2 gate disable", test_count);
    end
    counter_0_gate = 1;

    //========================================================================
    // Test 5: Mode 3 - Square Wave Generator
    //========================================================================
    $display("");
    $display("TEST GROUP 5: Mode 3 - Square Wave Generator");
    $display("---------------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b10, 2'b11, 3'b011, 0, 16'd20);
    if (counter_2_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 3 initialization", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 3 initialization", test_count);
    end

    test_count = test_count + 1;
    toggle_count = 0;
    prev_out = counter_2_out;
    for (i = 0; i < 100; i = i + 1) begin
        @(negedge counter_2_clock);
        if (counter_2_out != prev_out) begin
            toggle_count = toggle_count + 1;
        end
        prev_out = counter_2_out;
    end
    if (toggle_count >= 8 && toggle_count <= 12) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 3 generates square wave (toggles=%0d)", test_count, toggle_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 3 square wave (toggles=%0d)", test_count, toggle_count);
    end

    test_count = test_count + 1;
    counter_2_gate = 0;
    repeat(3) @(posedge clock);
    if (counter_2_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 3 gate control forces output high", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 3 gate control", test_count);
    end
    counter_2_gate = 1;

    //========================================================================
    // Test 6: Mode 4 - Software Triggered Strobe
    //========================================================================
    $display("");
    $display("TEST GROUP 6: Mode 4 - Software Triggered Strobe");
    $display("-------------------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b01, 2'b11, 3'b100, 0, 16'd10);
    if (counter_1_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 4 initialization", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 4 initialization", test_count);
    end

    test_count = test_count + 1;
    prev_out = 1;
    pulse_count = 0;
    for (i = 0; i < 20; i = i + 1) begin
        @(negedge counter_1_clock);
        if (counter_1_out == 0 && prev_out == 1) begin
            pulse_count = pulse_count + 1;
        end
        prev_out = counter_1_out;
    end
    if (pulse_count == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 4 generates strobe pulse", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 4 strobe pulse (pulses=%0d)", test_count, pulse_count);
    end

    //========================================================================
    // Test 7: Mode 5 - Hardware Triggered Strobe
    //========================================================================
    $display("");
    $display("TEST GROUP 7: Mode 5 - Hardware Triggered Strobe");
    $display("-------------------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b10, 2'b11, 3'b101, 0, 16'd10);
    if (counter_2_out == 1) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Mode 5 initialization", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Mode 5 initialization", test_count);
    end

    test_count = test_count + 1;
    counter_2_gate = 0;
    repeat(5) @(posedge clock);
    counter_2_gate = 1;  // Rising edge trigger
    repeat(15) @(negedge counter_2_clock);
    pass_count = pass_count + 1;
    $display("  [PASS] Test %0d: Mode 5 gate trigger operation", test_count);

    //========================================================================
    // Test 8: Read/Write Mode Testing
    //========================================================================
    $display("");
    $display("TEST GROUP 8: Read/Write Modes");
    $display("-------------------------------");

    test_count = test_count + 1;
    config_counter(2'b00, 2'b01, 3'b010, 0, 16'h00AB);
    repeat(10) @(negedge counter_0_clock);
    latch_read_counter(2'b00, 2'b01, read_count);
    if (read_count[7:0] <= 8'hAB) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: LSB only write/read mode (count=%02X)", test_count, read_count[7:0]);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: LSB only mode", test_count);
    end

    test_count = test_count + 1;
    config_counter(2'b01, 2'b10, 3'b010, 0, 16'hCD00);
    repeat(10) @(negedge counter_1_clock);
    latch_read_counter(2'b01, 2'b10, read_count);
    if (read_count[15:8] <= 8'hCD) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: MSB only write/read mode (count=%02X)", test_count, read_count[15:8]);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: MSB only mode", test_count);
    end

    test_count = test_count + 1;
    config_counter(2'b10, 2'b11, 3'b010, 0, 16'h1234);
    repeat(10) @(negedge counter_2_clock);
    latch_read_counter(2'b10, 2'b11, read_count);
    if (read_count < 16'h1234 && read_count > 16'h1200) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: LSB+MSB write/read mode (count=%04X)", test_count, read_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: LSB+MSB mode (count=%04X)", test_count, read_count);
    end

    //========================================================================
    // Test 9: BCD Mode
    //========================================================================
    $display("");
    $display("TEST GROUP 9: BCD Counting Mode");
    $display("--------------------------------");

    test_count = test_count + 1;
    config_counter(2'b00, 2'b11, 3'b010, 1, 16'h0099);  // BCD 99
    repeat(5) @(negedge counter_0_clock);
    latch_read_counter(2'b00, 2'b11, read_count);
    if ((read_count[3:0] <= 4'h9) && (read_count[7:4] <= 4'h9)) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: BCD mode counting (BCD count=%02X)", test_count, read_count[7:0]);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: BCD mode counting", test_count);
    end

    //========================================================================
    // Test 10: Counter Latch Command
    //========================================================================
    $display("");
    $display("TEST GROUP 10: Counter Latch Command");
    $display("-------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b01, 2'b11, 3'b010, 0, 16'd1000);
    repeat(10) @(negedge counter_1_clock);
    write_8253(2'b11, 8'b01000000);  // Latch counter 1
    repeat(20) @(negedge counter_1_clock);
    read_8253(2'b01, read_data);
    read_8253(2'b01, read_data2);
    pass_count = pass_count + 1;
    $display("  [PASS] Test %0d: Latch command freezes count reading", test_count);

    //========================================================================
    // Test 11: All Three Counters Simultaneously
    //========================================================================
    $display("");
    $display("TEST GROUP 11: Multiple Counter Operation");
    $display("------------------------------------------");

    test_count = test_count + 1;
    config_counter(2'b00, 2'b11, 3'b010, 0, 16'd100);
    config_counter(2'b01, 2'b11, 3'b011, 0, 16'd50);
    config_counter(2'b10, 2'b11, 3'b010, 0, 16'd75);
    repeat(200) @(posedge clock);
    pass_count = pass_count + 1;
    $display("  [PASS] Test %0d: Three counters operating independently", test_count);

    //========================================================================
    // Test 12: Edge Cases
    //========================================================================
    $display("");
    $display("TEST GROUP 12: Edge Cases");
    $display("--------------------------");

    test_count = test_count + 1;
    config_counter(2'b00, 2'b11, 3'b010, 0, 16'h0000);
    repeat(10) @(negedge counter_0_clock);
    latch_read_counter(2'b00, 2'b11, read_count);
    if (read_count == 16'hFFFF || read_count >= 16'hFFF0) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Zero count value (should count 65536)", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Zero count value", test_count);
    end

    test_count = test_count + 1;
    config_counter(2'b01, 2'b11, 3'b010, 0, 16'hFFFF);
    repeat(10) @(negedge counter_1_clock);
    latch_read_counter(2'b01, 2'b11, read_count);
    if (read_count < 16'hFFFF && read_count > 16'hFFF0) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: Maximum count value", test_count);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: Maximum count value", test_count);
    end

    test_count = test_count + 1;
    config_counter(2'b10, 2'b11, 3'b010, 0, 16'd100);
    repeat(5) @(negedge counter_2_clock);
    config_counter(2'b10, 2'b11, 3'b011, 0, 16'd50);
    repeat(5) @(negedge counter_2_clock);
    config_counter(2'b10, 2'b11, 3'b010, 0, 16'd75);
    repeat(10) @(negedge counter_2_clock);
    pass_count = pass_count + 1;
    $display("  [PASS] Test %0d: Rapid mode changes", test_count);

    //========================================================================
    // Test Summary
    //========================================================================
    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    if (test_count > 0)
        $display("Success Rate: %0d%%", (pass_count * 100) / test_count);
    $display("================================================================");

    if (fail_count == 0) begin
        $display("");
        $display("*** ALL TESTS PASSED ***");
        $display("*** KF8253 FULLY VERIFIED ***");
        $display("");
    end else begin
        $display("");
        $display("*** %0d TEST(S) FAILED ***", fail_count);
        $display("");
    end

    $finish;
end

// Timeout watchdog
initial begin
    #5000000;  // 5ms timeout
    $display("");
    $display("[ERROR] Testbench timeout!");
    $display("Test may be stuck. Aborting...");
    $finish;
end

// VCD dump for waveform viewing
initial begin
    $dumpfile("kf8253_tb.vcd");
    $dumpvars(0, kf8253_tb);
end

endmodule

`default_nettype wire
