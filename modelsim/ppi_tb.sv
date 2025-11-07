//============================================================================
//
//  PPI (8255) Testbench
//  Verifies Programmable Peripheral Interface functionality for PC compatibility
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module ppi_tb;

// Clock and reset
reg clk;
reg reset;

// PPI interface
reg         chip_select;
reg         read_enable;
reg         write_enable;
reg  [1:0]  address;       // 00=Port A, 01=Port B, 10=Port C, 11=Control
reg  [7:0]  data_bus_in;
wire [7:0]  data_bus_out;
wire        ack;

// Port A - Typically keyboard data
reg  [7:0]  port_a_in;
wire [7:0]  port_a_out;
wire        port_a_io;     // 0=output, 1=input

// Port B - Typically system control
reg  [7:0]  port_b_in;
wire [7:0]  port_b_out;
wire        port_b_io;

// Port C - Control/status signals
reg  [7:0]  port_c_in;
wire [7:0]  port_c_out;
wire [7:0]  port_c_io;     // Individual bit control

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// Helper variables
reg [7:0] read_data;
integer bit_test_pass;
integer bit_num;

// DUT instantiation
KF8255 dut (
    .clock          (clk),
    .reset          (reset),
    .chip_select    (chip_select),
    .read_enable    (read_enable),
    .write_enable   (write_enable),
    .address        (address),
    .data_bus_in    (data_bus_in),
    .data_bus_out   (data_bus_out),
    .ack            (ack),
    .port_a_in      (port_a_in),
    .port_a_out     (port_a_out),
    .port_a_io      (port_a_io),
    .port_b_in      (port_b_in),
    .port_b_out     (port_b_out),
    .port_b_io      (port_b_io),
    .port_c_in      (port_c_in),
    .port_c_out     (port_c_out),
    .port_c_io      (port_c_io)
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 20ns period = 50 MHz
end

// Helper task for writing to PPI
task write_ppi(input [1:0] addr, input [7:0] data);
    begin
        chip_select = 1'b1;
        write_enable = 1'b1;
        read_enable = 1'b0;
        address = addr;
        data_bus_in = data;
        @(posedge clk);
        chip_select = 1'b0;
        write_enable = 1'b0;
        @(posedge clk);
    end
endtask

// Helper task for reading from PPI
task read_ppi(input [1:0] addr, output [7:0] data);
    begin
        chip_select = 1'b1;
        write_enable = 1'b0;
        read_enable = 1'b1;
        address = addr;
        @(posedge clk);
        @(posedge clk);
        data = data_bus_out;
        chip_select = 1'b0;
        read_enable = 1'b0;
        @(posedge clk);
    end
endtask

// Test stimulus
initial begin
    $display("================================================================");
    $display("PPI (8255) Testbench");
    $display("Testing Programmable Peripheral Interface for PC compatibility");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1;
    chip_select = 0;
    read_enable = 0;
    write_enable = 0;
    address = 2'b00;
    data_bus_in = 8'h00;
    port_a_in = 8'h00;
    port_b_in = 8'h00;
    port_c_in = 8'h00;

    // Wait for reset
    repeat(10) @(posedge clk);
    reset = 0;
    repeat(5) @(posedge clk);

    $display("Test 1: Configure Mode 0 - All ports as outputs");
    test_count++;
    // Control word: 1_000_0_000 = 0x80
    // Bit 7: Mode set flag (1)
    // Bits 6-5: Group A mode (00 = Mode 0)
    // Bit 4: Port A direction (0 = output)
    // Bit 3: Port C upper direction (0 = output)
    // Bit 2: Group B mode (0 = Mode 0)
    // Bit 1: Port B direction (0 = output)
    // Bit 0: Port C lower direction (0 = output)
    write_ppi(2'b11, 8'h80);
    repeat(5) @(posedge clk);

    if (port_a_io == 1'b0 && port_b_io == 1'b0) begin
        $display("  [PASS] Mode 0 configured, ports set as outputs");
        pass_count++;
    end else begin
        $display("  [FAIL] Port directions incorrect (A_io=%b, B_io=%b)", port_a_io, port_b_io);
        fail_count++;
    end

    $display("");
    $display("Test 2: Write to Port A and verify output");
    test_count++;
    write_ppi(2'b00, 8'hAA);  // Write 0xAA to Port A
    repeat(5) @(posedge clk);

    if (port_a_out == 8'hAA) begin
        $display("  [PASS] Port A output = 0x%02X", port_a_out);
        pass_count++;
    end else begin
        $display("  [FAIL] Port A output = 0x%02X (expected 0xAA)", port_a_out);
        fail_count++;
    end

    $display("");
    $display("Test 3: Write to Port B and verify output");
    test_count++;
    write_ppi(2'b01, 8'h55);  // Write 0x55 to Port B
    repeat(5) @(posedge clk);

    if (port_b_out == 8'h55) begin
        $display("  [PASS] Port B output = 0x%02X", port_b_out);
        pass_count++;
    end else begin
        $display("  [FAIL] Port B output = 0x%02X (expected 0x55)", port_b_out);
        fail_count++;
    end

    $display("");
    $display("Test 4: Write to Port C and verify output");
    test_count++;
    write_ppi(2'b10, 8'hF0);  // Write 0xF0 to Port C
    repeat(5) @(posedge clk);

    if (port_c_out == 8'hF0) begin
        $display("  [PASS] Port C output = 0x%02X", port_c_out);
        pass_count++;
    end else begin
        $display("  [FAIL] Port C output = 0x%02X (expected 0xF0)", port_c_out);
        fail_count++;
    end

    $display("");
    $display("Test 5: Configure Mode 0 - All ports as inputs");
    test_count++;
    // Control word: 1_001_1_011 = 0x9B
    write_ppi(2'b11, 8'h9B);
    repeat(5) @(posedge clk);

    if (port_a_io == 1'b1 && port_b_io == 1'b1) begin
        $display("  [PASS] Ports configured as inputs");
        pass_count++;
    end else begin
        $display("  [FAIL] Port directions incorrect (A_io=%b, B_io=%b)", port_a_io, port_b_io);
        fail_count++;
    end

    $display("");
    $display("Test 6: Read from Port A (input mode)");
    test_count++;
    port_a_in = 8'h3C;  // Set external input
    repeat(5) @(posedge clk);
    read_ppi(2'b00, read_data);

    if (read_data == 8'h3C) begin
        $display("  [PASS] Port A read = 0x%02X", read_data);
        pass_count++;
    end else begin
        $display("  [FAIL] Port A read = 0x%02X (expected 0x3C)", read_data);
        fail_count++;
    end

    $display("");
    $display("Test 7: Read from Port B (input mode)");
    test_count++;
    port_b_in = 8'hC3;  // Set external input
    repeat(5) @(posedge clk);
    read_ppi(2'b01, read_data);

    if (read_data == 8'hC3) begin
        $display("  [PASS] Port B read = 0x%02X", read_data);
        pass_count++;
    end else begin
        $display("  [FAIL] Port B read = 0x%02X (expected 0xC3)", read_data);
        fail_count++;
    end

    $display("");
    $display("Test 8: Read from Port C (input mode)");
    test_count++;
    port_c_in = 8'h0F;  // Set external input
    repeat(5) @(posedge clk);
    read_ppi(2'b10, read_data);

    if (read_data == 8'h0F) begin
        $display("  [PASS] Port C read = 0x%02X", read_data);
        pass_count++;
    end else begin
        $display("  [FAIL] Port C read = 0x%02X (expected 0x0F)", read_data);
        fail_count++;
    end

    $display("");
    $display("Test 9: Port C bit set/reset (BSR mode)");
    test_count++;
    // First set all outputs
    write_ppi(2'b11, 8'h80);  // All outputs
    write_ppi(2'b10, 8'h00);  // Clear Port C
    repeat(5) @(posedge clk);

    // BSR: Set bit 3 of Port C
    // Control word: 0_xxx_0_011_1 = 0x07 (bit 3, set)
    write_ppi(2'b11, 8'h07);
    repeat(5) @(posedge clk);

    if (port_c_out[3] == 1'b1) begin
        $display("  [PASS] Port C bit 3 set via BSR");
        pass_count++;
    end else begin
        $display("  [FAIL] Port C bit 3 not set (Port C = 0x%02X)", port_c_out);
        fail_count++;
    end

    $display("");
    $display("Test 10: Port C bit reset via BSR");
    test_count++;
    // BSR: Reset bit 3 of Port C
    // Control word: 0_xxx_0_011_0 = 0x06 (bit 3, reset)
    write_ppi(2'b11, 8'h06);
    repeat(5) @(posedge clk);

    if (port_c_out[3] == 1'b0) begin
        $display("  [PASS] Port C bit 3 cleared via BSR");
        pass_count++;
    end else begin
        $display("  [FAIL] Port C bit 3 not cleared (Port C = 0x%02X)", port_c_out);
        fail_count++;
    end

    $display("");
    $display("Test 11: Mixed I/O configuration - Port A input, Port B output");
    test_count++;
    // Control word: 1_001_0_001 = 0x92
    // Port A = input, Port B = output
    write_ppi(2'b11, 8'h92);
    repeat(5) @(posedge clk);

    // Write to Port B (output)
    write_ppi(2'b01, 8'hBB);
    // Set Port A input
    port_a_in = 8'h77;
    repeat(5) @(posedge clk);

    // Read Port A
    read_ppi(2'b00, read_data);

    if (read_data == 8'h77 && port_b_out == 8'hBB) begin
        $display("  [PASS] Mixed I/O: Port A input=0x%02X, Port B output=0x%02X",
                 read_data, port_b_out);
        pass_count++;
    end else begin
        $display("  [FAIL] Mixed I/O failed (A=0x%02X, B=0x%02X)", read_data, port_b_out);
        fail_count++;
    end

    $display("");
    $display("Test 12: Verify ACK signal generation");
    test_count++;
    chip_select = 1'b1;
    read_enable = 1'b1;
    address = 2'b00;
    @(posedge clk);

    if (ack) begin
        $display("  [PASS] ACK signal asserted on read");
        pass_count++;
    end else begin
        $display("  [FAIL] ACK signal not asserted");
        fail_count++;
    end

    chip_select = 1'b0;
    read_enable = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 13: PC/XT keyboard interface simulation");
    test_count++;
    $display("  [INFO] PC/XT PPI Usage:");
    $display("    Port A: Keyboard scancode input");
    $display("    Port B: System control (speaker, etc.)");
    $display("    Port C: Keyboard control/status");

    // Configure for PC/XT: Port A input, Port B output, Port C mixed
    write_ppi(2'b11, 8'h99);  // Port A in, B out, C upper in, C lower out

    // Simulate keyboard scancode
    port_a_in = 8'h1E;  // Scancode for 'A' key
    repeat(5) @(posedge clk);

    // Read scancode
    read_ppi(2'b00, read_data);

    if (read_data == 8'h1E) begin
        $display("  [PASS] Keyboard scancode read correctly (0x%02X)", read_data);
        pass_count++;
    end else begin
        $display("  [FAIL] Keyboard scancode incorrect (got 0x%02X)", read_data);
        fail_count++;
    end

    $display("");
    $display("Test 14: PC speaker control simulation (Port B bit 1)");
    test_count++;
    // Write to Port B to control speaker
    write_ppi(2'b01, 8'h03);  // Enable speaker (bits 0 and 1)
    repeat(5) @(posedge clk);

    if (port_b_out[1] == 1'b1) begin
        $display("  [PASS] Speaker enable bit set (Port B = 0x%02X)", port_b_out);
        pass_count++;
    end else begin
        $display("  [FAIL] Speaker enable bit not set (Port B = 0x%02X)", port_b_out);
        fail_count++;
    end

    $display("");
    $display("Test 15: Multiple rapid writes");
    test_count++;
    write_ppi(2'b00, 8'h11);
    write_ppi(2'b00, 8'h22);
    write_ppi(2'b00, 8'h33);
    write_ppi(2'b00, 8'hFF);
    repeat(5) @(posedge clk);

    if (port_a_out == 8'hFF) begin
        $display("  [PASS] Rapid writes handled correctly (final value = 0x%02X)", port_a_out);
        pass_count++;
    end else begin
        $display("  [FAIL] Rapid write handling issue (got 0x%02X)", port_a_out);
        fail_count++;
    end

    $display("");
    $display("Test 16: All Port C bits BSR test");
    test_count++;
    bit_test_pass = 1;

    // Configure Port C as output
    write_ppi(2'b11, 8'h80);
    write_ppi(2'b10, 8'h00);  // Clear all

    // Test setting each bit
    for (bit_num = 0; bit_num < 8; bit_num = bit_num + 1) begin
        write_ppi(2'b11, {1'b0, 4'b0, bit_num[2:0], 1'b1});  // Set bit
        repeat(3) @(posedge clk);
        if (port_c_out[bit_num] != 1'b1) begin
            bit_test_pass = 0;
            $display("    [FAIL] Bit %0d set failed", bit_num);
        end
        write_ppi(2'b11, {1'b0, 4'b0, bit_num[2:0], 1'b0});  // Clear bit
        repeat(3) @(posedge clk);
        if (port_c_out[bit_num] != 1'b0) begin
            bit_test_pass = 0;
            $display("    [FAIL] Bit %0d clear failed", bit_num);
        end
    end

    if (bit_test_pass) begin
        $display("  [PASS] All Port C BSR operations successful");
        pass_count++;
    end else begin
        $display("  [FAIL] Some Port C BSR operations failed");
        fail_count++;
    end

    $display("");
    $display("Test 17: PC compatibility check");
    test_count++;
    $display("  [INFO] Standard PC PPI configuration:");
    $display("    I/O Ports: 0x60-0x63");
    $display("    0x60: Port A - Keyboard data");
    $display("    0x61: Port B - System control");
    $display("    0x62: Port C - Keyboard/system status");
    $display("    0x63: Control register");

    // Standard PC initialization
    write_ppi(2'b11, 8'h99);  // Port A input, B output, C mixed

    // Verify configuration
    repeat(5) @(posedge clk);
    if (port_a_io == 1'b1 && port_b_io == 1'b0) begin
        $display("  [PASS] Standard PC PPI configuration successful");
        pass_count++;
    end else begin
        $display("  [FAIL] PC configuration incorrect");
        fail_count++;
    end

    // Test Summary
    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0d%%", (pass_count * 100) / test_count);
    $display("================================================================");

    if (fail_count == 0) begin
        $display("");
        $display("*** ALL TESTS PASSED ***");
        $display("*** PC PPI COMPATIBILITY VERIFIED ***");
        $display("");
    end else begin
        $display("");
        $display("*** SOME TESTS FAILED ***");
        $display("");
    end

    $finish;
end

// VCD dump for waveform viewing
initial begin
    $dumpfile("ppi_tb.vcd");
    $dumpvars(0, ppi_tb);
end

endmodule

`default_nettype wire
