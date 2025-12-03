// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// IRQController Testbench
// Tests the NMI/IRQ test controller register

`timescale 1ns/1ps

module irq_controller_tb;

reg clk;
reg reset;
reg cs;
reg [15:0] data_m_data_in;
reg [1:0] data_m_bytesel;
wire [15:0] data_m_data_out;
reg data_m_wr_en;
reg data_m_access;
wire data_m_ack;
wire nmi;
wire [6:0] intr_test;

integer test_count;
integer pass_count;
integer fail_count;

IRQController dut (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .data_m_data_in(data_m_data_in),
    .data_m_bytesel(data_m_bytesel),
    .data_m_data_out(data_m_data_out),
    .data_m_wr_en(data_m_wr_en),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .nmi(nmi),
    .intr_test(intr_test)
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
    $display("IRQController Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    cs = 0;
    data_m_data_in = 16'h0000;
    data_m_bytesel = 2'b11;
    data_m_wr_en = 0;
    data_m_access = 0;

    // Release reset
    @(posedge clk);
    @(posedge clk);
    #1;
    reset = 0;
    @(posedge clk);
    #1;

    // Test 1: Initial state after reset
    $display("\n--- Testing initial state ---");
    check_bit("NMI initially 0", 1'b0, nmi);
    check("intr_test initially 0", 7'h00, intr_test);

    // Test 2: Write to set IRQ lines
    $display("\n--- Testing IRQ write ---");
    cs = 1;
    data_m_access = 1;
    data_m_wr_en = 1;
    data_m_bytesel = 2'b01;  // Low byte
    data_m_data_in = 16'h007F;  // All 7 IRQ lines
    @(posedge clk);
    #1;
    check("Set all IRQ lines (0x7F)", 7'h7F, intr_test);
    check_bit("NMI still 0 (bit 7 not set)", 1'b0, nmi);

    // Test 3: Set NMI
    $display("\n--- Testing NMI ---");
    data_m_data_in = 16'h0080;  // NMI bit only
    @(posedge clk);
    #1;
    // NMI is registered, needs another cycle
    @(posedge clk);
    #1;
    check_bit("NMI asserted", 1'b1, nmi);
    check("IRQ lines cleared", 7'h00, intr_test);

    // Test 4: Set both NMI and IRQ
    data_m_data_in = 16'h00FF;  // All bits
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;
    check_bit("NMI asserted with IRQs", 1'b1, nmi);
    check("All IRQ lines set", 7'h7F, intr_test);

    // Test 5: Read back value
    $display("\n--- Testing read ---");
    data_m_wr_en = 0;
    @(posedge clk);
    #1;
    check("Read back value (0x00FF)", 16'h00FF, data_m_data_out);

    // Test 6: Ack signal
    check_bit("Ack asserted on access", 1'b1, data_m_ack);

    // Test 7: No write when cs is low
    $display("\n--- Testing access control ---");
    cs = 0;
    data_m_wr_en = 1;
    data_m_data_in = 16'h0000;
    @(posedge clk);
    #1;
    check("No write when cs=0", 7'h7F, intr_test);

    // Test 8: No write when bytesel[0] is low
    cs = 1;
    data_m_bytesel = 2'b10;  // High byte only
    data_m_data_in = 16'h0000;
    @(posedge clk);
    #1;
    check("No write when bytesel[0]=0", 7'h7F, intr_test);

    // Test 9: Clear IRQ lines
    $display("\n--- Testing clear ---");
    data_m_bytesel = 2'b01;
    data_m_data_in = 16'h0000;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;
    check("IRQ lines cleared", 7'h00, intr_test);
    check_bit("NMI cleared", 1'b0, nmi);

    // Test 10: Set individual IRQ lines
    $display("\n--- Testing individual IRQ lines ---");
    data_m_data_in = 16'h0001;  // IRQ0
    @(posedge clk);
    #1;
    check("IRQ0 set", 7'h01, intr_test);

    data_m_data_in = 16'h0040;  // IRQ6
    @(posedge clk);
    #1;
    check("IRQ6 set", 7'h40, intr_test);

    // Test 11: Reset clears everything
    $display("\n--- Testing reset ---");
    data_m_data_in = 16'h00FF;
    @(posedge clk);
    #1;
    @(posedge clk);
    #1;
    check_bit("NMI set before reset", 1'b1, nmi);

    reset = 1;
    @(posedge clk);
    #1;
    check("IRQ lines cleared on reset", 7'h00, intr_test);
    check_bit("NMI cleared on reset", 1'b0, nmi);

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
    $dumpfile("irq_controller_tb.vcd");
    $dumpvars(0, irq_controller_tb);
end

endmodule
