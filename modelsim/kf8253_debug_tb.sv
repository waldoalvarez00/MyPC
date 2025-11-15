//============================================================================
//
//  KF8253 Debug Testbench - Detailed Tracing
//  Minimal test with extensive debug output
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

`include "KF8253_Definitions.svh"

module kf8253_debug_tb;

// Clock and reset
reg clock;
reg reset;

// Counter 0 signals
reg counter_0_clock;
reg counter_0_gate;
wire counter_0_out;

// Unused counters (tied off)
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

// Test variables
reg [7:0] lsb, msb;

// DUT
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
    forever #10 clock = ~clock;
end

// Counter clock - needs to be driven explicitly
task pulse_counter_0_clock;
    begin
        @(posedge clock);
        counter_0_clock = 1;
        @(posedge clock);
        counter_0_clock = 0;
        @(posedge clock);
    end
endtask

// Write task
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
        $display("[%0t] WRITE: addr=%b data=%02X", $time, addr, data);
        @(posedge clock);
        write_enable_n = 1'b1;
        chip_select_n = 1'b1;
        @(posedge clock);
    end
endtask

// Read task
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
        $display("[%0t] READ: addr=%b data=%02X", $time, addr, data);
        read_enable_n = 1'b1;
        chip_select_n = 1'b1;
        @(posedge clock);
    end
endtask

// Main test
initial begin
    $display("================================================================");
    $display("KF8253 Debug Testbench - Detailed Tracing");
    $display("================================================================\n");

    // Initialize
    reset = 1;
    chip_select_n = 1;
    read_enable_n = 1;
    write_enable_n = 1;
    address = 0;
    data_bus_in = 0;
    counter_0_gate = 1;
    counter_0_clock = 0;
    counter_1_gate = 1;
    counter_1_clock = 0;
    counter_2_gate = 1;
    counter_2_clock = 0;

    repeat(10) @(posedge clock);
    reset = 0;
    $display("[%0t] Reset released\n", $time);
    repeat(5) @(posedge clock);

    // Test 1: Configure Counter 0 in Mode 2, count=10
    $display("Test 1: Configure Counter 0 - Mode 2, Count=10");
    $display("------------------------------------------------");

    // Control word: Counter 0, LSB+MSB, Mode 2, Binary
    // Bits: SC=00, RW=11, M=010, BCD=0 = 0011_0100 = 0x34
    write_8253(2'b11, 8'h34);

    $display("Writing count LSB=10");
    write_8253(2'b00, 8'd10);

    $display("Writing count MSB=0");
    write_8253(2'b00, 8'd0);

    $display("\nCounter state after config:");
    $display("  counter_0_out = %b", counter_0_out);
    repeat(5) @(posedge clock);

    // Pulse counter clock and observe
    $display("\nPulsing counter clock 5 times...");
    repeat(5) begin
        pulse_counter_0_clock();
        $display("  [%0t] After pulse: counter_0_out = %b", $time, counter_0_out);
    end

    // Try to read counter
    $display("\nLatching and reading counter...");
    write_8253(2'b11, 8'b00_00_000_0);  // Latch counter 0

    read_8253(2'b00, lsb);
    read_8253(2'b00, msb);
    $display("Counter value: %02X%02X (decimal %0d)", msb, lsb, {msb, lsb});

    // Continue pulsing to see if we reach terminal count
    $display("\nPulsing 10 more times to reach terminal count...");
    repeat(10) begin
        pulse_counter_0_clock();
        $display("  [%0t] After pulse: counter_0_out = %b", $time, counter_0_out);
    end

    // Test 2: Mode 0 (simpler)
    $display("\n\nTest 2: Configure Counter 0 - Mode 0, Count=5");
    $display("-----------------------------------------------");

    // Control word: Counter 0, LSB+MSB, Mode 0, Binary = 0x30
    write_8253(2'b11, 8'h30);
    write_8253(2'b00, 8'd5);
    write_8253(2'b00, 8'd0);

    $display("Counter state after config:");
    $display("  counter_0_out = %b", counter_0_out);
    repeat(5) @(posedge clock);

    $display("\nPulsing counter clock until terminal count...");
    repeat(10) begin
        pulse_counter_0_clock();
        $display("  [%0t] After pulse %0d: counter_0_out = %b", $time, counter_0_out);
        if (counter_0_out == 1) begin
            $display("  *** Terminal count reached! ***");
        end
    end

    $display("\n================================================================");
    $display("Debug test complete");
    $display("================================================================");
    $finish;
end

// Monitor internal signals (if available)
initial begin
    $display("\nMonitoring internal counter 0 signals:");
    forever begin
        @(posedge clock);
        if (!reset) begin
            // Note: These signals may not be visible depending on hierarchy
            $display("[%0t] Internal: start_counting=%b, count_edge=%b",
                     $time,
                     dut.u_KF8253_Counter_0.start_counting,
                     dut.u_KF8253_Counter_0.count_edge);
        end
    end
end

// VCD dump
initial begin
    $dumpfile("kf8253_debug.vcd");
    $dumpvars(0, kf8253_debug_tb);
    $dumpvars(0, dut.u_KF8253_Counter_0);
end

// Timeout
initial begin
    #500000;
    $display("\n[ERROR] Timeout!");
    $finish;
end

endmodule

`default_nettype wire
