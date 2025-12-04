`timescale 1ns/1ps

module RegisterFile_tb;

// Parameters
parameter CLK_PERIOD = 10;

// Testbench signals
logic clk;
logic reset;
logic is_8_bit;
logic [15:0] si, di, bp, bx;
logic [2:0] rd_sel_0, rd_sel_1;
logic [15:0] rd_val_0, rd_val_1;
logic [2:0] wr_sel;
logic [15:0] wr_val;
logic wr_en;

// Test statistics
integer test_count = 0;
integer pass_count = 0;
integer fail_count = 0;

// Instantiate the RegisterFile through wrapper (Icarus compatibility)
RegisterFile_wrapper uut (
    .clk(clk),
    .reset(reset),
    .is_8_bit(is_8_bit),
    .si(si),
    .di(di),
    .bp(bp),
    .bx(bx),
    .rd_sel_0(rd_sel_0),
    .rd_val_0(rd_val_0),
    .rd_sel_1(rd_sel_1),
    .rd_val_1(rd_val_1),
    .wr_sel(wr_sel),
    .wr_val(wr_val),
    .wr_en(wr_en)
);

// Clock generation
always #(CLK_PERIOD/2) clk = ~clk;

// Test task
task automatic check_result(input string test_name, input logic [15:0] expected, input logic [15:0] actual);
    test_count++;
    if (expected === actual) begin
        $display("[PASS] %s: Expected 0x%04h, Got 0x%04h", test_name, expected, actual);
        pass_count++;
    end else begin
        $display("[FAIL] %s: Expected 0x%04h, Got 0x%04h", test_name, expected, actual);
        fail_count++;
    end
endtask

// Helper task for write with proper timing
task do_write(input [2:0] sel, input [15:0] val);
    #1;
    wr_sel = sel;
    wr_val = val;
    wr_en = 1;
    #1;
    @(posedge clk);
    #1;
    wr_en = 0;
    #1;
    @(posedge clk);
    #1;
endtask

// Helper task for read with proper timing (port 0)
task do_read_0(input [2:0] sel);
    #1;
    rd_sel_0 = sel;
    #1;
    @(posedge clk);
    @(posedge clk);
    #1;
endtask

// Main test sequence
initial begin
    $display("========================================");
    $display("RegisterFile Testbench Started");
    $display("========================================");

    // Initialize signals
    clk = 0;
    reset = 1;
    is_8_bit = 0;
    rd_sel_0 = 3'b000;
    rd_sel_1 = 3'b000;
    wr_sel = 3'b000;
    wr_val = 16'h0000;
    wr_en = 0;

    // Reset pulse
    #(CLK_PERIOD * 2);
    reset = 0;
    #(CLK_PERIOD * 2);
    #1;

    //========================================
    // TEST 1: 16-bit Register Writes
    //========================================
    $display("\n--- TEST 1: 16-bit Register Writes ---");
    is_8_bit = 0;

    // Write to AX (000)
    do_write(3'b000, 16'h1234);
    do_read_0(3'b000);
    check_result("Write/Read AX", 16'h1234, rd_val_0);

    // Write to CX (001)
    do_write(3'b001, 16'h5678);
    do_read_0(3'b001);
    check_result("Write/Read CX", 16'h5678, rd_val_0);

    // Write to DX (010)
    do_write(3'b010, 16'h9ABC);
    do_read_0(3'b010);
    check_result("Write/Read DX", 16'h9ABC, rd_val_0);

    // Write to BX (011) - BX has direct output port
    do_write(3'b011, 16'hDEF0);
    check_result("BX output port", 16'hDEF0, bx);

    //========================================
    // TEST 2: 8-bit Register Writes (Low Byte)
    //========================================
    $display("\n--- TEST 2: 8-bit Register Writes (Low Byte) ---");

    // First write a known 16-bit value to AX
    is_8_bit = 0;
    do_write(3'b000, 16'h1200);

    // Now write to AL (low byte)
    is_8_bit = 1;
    do_write(3'b000, 16'h00AA);

    // Read AX (16-bit mode)
    is_8_bit = 0;
    do_read_0(3'b000);
    check_result("Write AL, Read AX", 16'h12AA, rd_val_0);

    //========================================
    // TEST 3: 8-bit Register Writes (High Byte)
    //========================================
    $display("\n--- TEST 3: 8-bit Register Writes (High Byte) ---");

    // Write to AH (high byte)
    is_8_bit = 1;
    do_write(3'b100, 16'h00BB);

    // Read AX (16-bit mode)
    is_8_bit = 0;
    do_read_0(3'b000);
    check_result("Write AH, Read AX", 16'hBBAA, rd_val_0);

    //========================================
    // TEST 4: Dual Read Ports
    //========================================
    $display("\n--- TEST 4: Dual Read Ports ---");
    is_8_bit = 0;

    // Read AX and CX simultaneously
    #1;
    rd_sel_0 = 3'b000; // AX
    rd_sel_1 = 3'b001; // CX
    #1;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("Read Port 0 (AX)", 16'hBBAA, rd_val_0);
    check_result("Read Port 1 (CX)", 16'h5678, rd_val_1);

    //========================================
    // TEST 5: Write-Read Bypass
    //========================================
    $display("\n--- TEST 5: Write-Read Bypass ---");
    is_8_bit = 0;

    // Set up read port
    #1;
    rd_sel_0 = 3'b010; // DX
    wr_sel = 3'b010;   // DX
    wr_val = 16'hFFFF;
    wr_en = 1;
    #1;
    @(posedge clk);
    @(posedge clk);
    #1;
    check_result("Bypass Logic", 16'hFFFF, rd_val_0);
    wr_en = 0;
    #1;
    @(posedge clk);

    //========================================
    // TEST 6: Special Register Outputs (SI, DI, BP, BX)
    //========================================
    $display("\n--- TEST 6: Special Register Outputs ---");
    is_8_bit = 0;

    // Write to SI (110)
    do_write(3'b110, 16'hA5A5);
    check_result("SI output port", 16'hA5A5, si);

    // Write to DI (111)
    do_write(3'b111, 16'h5A5A);
    check_result("DI output port", 16'h5A5A, di);

    // Write to BP (101)
    do_write(3'b101, 16'h3C3C);
    check_result("BP output port", 16'h3C3C, bp);

    //========================================
    // TEST 7: 8-bit BL/BH Register Operations
    //========================================
    $display("\n--- TEST 7: 8-bit BL/BH Register Operations ---");

    // First write a known value to BX
    is_8_bit = 0;
    do_write(3'b011, 16'h0000);

    // Write to BL (011)
    is_8_bit = 1;
    do_write(3'b011, 16'h00CC);
    check_result("BX after BL write", 16'h00CC, bx);

    // Write to BH (111)
    do_write(3'b111, 16'h00DD);
    check_result("BX after BH write", 16'hDDCC, bx);

    //========================================
    // Test Summary
    //========================================
    #(CLK_PERIOD * 5);
    $display("\n========================================");
    $display("RegisterFile Testbench Complete");
    $display("========================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    if (fail_count == 0)
        $display("STATUS: ALL TESTS PASSED!");
    else
        $display("STATUS: SOME TESTS FAILED!");
    $display("========================================");

    if (fail_count == 0)
        $finish(0);
    else
        $finish(1);
end

// Timeout watchdog
initial begin
    #50000;
    $display("ERROR: Testbench timeout!");
    $finish(1);
end

endmodule
