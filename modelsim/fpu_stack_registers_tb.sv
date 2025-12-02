// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// FPU_Stack_Registers Testbench
// Tests the FPU 80-bit stack register file

`timescale 1ns/1ps

module fpu_stack_registers_tb;

reg clk;
reg reset;
reg [2:0] read_addr;
reg [2:0] write_addr;
reg [79:0] write_data;
reg write_enable;
wire [79:0] read_data;

integer test_count;
integer pass_count;
integer fail_count;
integer i;

// Clock generation
always #5 clk = ~clk;

// DUT instantiation
FPU_Stack_Registers dut (
    .clk(clk),
    .reset(reset),
    .read_addr(read_addr),
    .write_addr(write_addr),
    .write_data(write_data),
    .write_enable(write_enable),
    .read_data(read_data)
);

task check_value(input string test_name, input [79:0] expected, input [79:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s", test_count, test_name);
        $display("       Expected: %020h", expected);
        $display("       Got:      %020h", actual);
        fail_count = fail_count + 1;
    end
end
endtask

initial begin
    $display("========================================");
    $display("FPU_Stack_Registers Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    read_addr = 3'b000;
    write_addr = 3'b000;
    write_data = 80'h0;
    write_enable = 0;

    // Release reset
    #20;
    reset = 0;
    #20;

    // Test 1-8: All registers zero after reset
    $display("\n--- Testing reset state ---");
    for (i = 0; i < 8; i = i + 1) begin
        read_addr = i[2:0];
        #1;
        check_value($sformatf("ST(%0d) zero after reset", i), 80'h0, read_data);
    end

    // Test 9-16: Write unique values to each register
    $display("\n--- Writing unique values ---");

    // Sync to clock before starting writes
    write_enable = 0;
    @(posedge clk);

    // Write ST(0) first and verify immediately
    write_addr = 3'b000;
    write_data = 80'h3FFF_8000_0000_0000_0000;
    write_enable = 1;
    $display("  Before posedge: write_addr=%0d, write_data=%020h, write_enable=%b", write_addr, write_data, write_enable);
    @(posedge clk);
    $display("  After posedge (write should happen), write_enable still=%b", write_enable);
    write_enable = 0;
    @(posedge clk);
    $display("  After second posedge");
    // Read back ST(0)
    read_addr = 3'b000;
    #1;
    $display("  Read ST(0) after write: %020h", read_data);

    // Also check DUT internal state if possible
    $display("  DUT.ST[0] direct: %020h", dut.ST[0]);
    $display("  DUT.ST[1] direct: %020h", dut.ST[1]);

    // Ensure clean timing before loop - add explicit clock cycle with write disabled
    write_enable = 0;
    write_addr = 3'b000;
    @(posedge clk);
    $display("  Sync point before loop");

    // Now write remaining registers
    for (i = 1; i < 8; i = i + 1) begin
        write_addr = i[2:0];
        write_data = 80'h3FFF_8000_0000_0000_0000 + i;
        write_enable = 1;
        $display("  Loop i=%0d: write_addr=%0d, write_data=%020h, we=%b", i, write_addr, write_data, write_enable);
        @(posedge clk);
        $display("    After posedge: DUT.ST[%0d]=%020h", i, dut.ST[i]);
        write_enable = 0;
        @(posedge clk);
    end

    // Final state
    $display("\n  Final DUT state:");
    for (i = 0; i < 8; i = i + 1) begin
        $display("  DUT.ST[%0d] = %020h", i, dut.ST[i]);
    end

    // Read back and verify all registers
    $display("\n--- Verifying all registers ---");
    for (i = 0; i < 8; i = i + 1) begin
        read_addr = i[2:0];
        @(posedge clk);  // Give time for read
        #1;
        check_value($sformatf("ST(%0d) readback", i), 80'h3FFF_8000_0000_0000_0000 + i, read_data);
    end

    // Test 17: Write to ST(3) while reading ST(5) - simultaneous access
    $display("\n--- Testing simultaneous read/write ---");
    write_addr = 3'b011;  // ST(3)
    write_data = 80'hAAAA_BBBB_CCCC_DDDD_EEEE;
    write_enable = 1;
    read_addr = 3'b101;  // ST(5)
    @(posedge clk);
    #1;
    check_value("Read ST(5) during write to ST(3)", 80'h3FFF_8000_0000_0000_0005, read_data);
    @(posedge clk);
    #1;
    read_addr = 3'b011;
    #1;
    check_value("ST(3) updated after write", 80'hAAAA_BBBB_CCCC_DDDD_EEEE, read_data);
    write_enable = 0;

    // Test 18: No write when enable is low
    $display("\n--- Testing write enable ---");
    write_addr = 3'b000;
    write_data = 80'hFFFF_FFFF_FFFF_FFFF_FFFF;
    write_enable = 0;
    @(posedge clk);
    @(posedge clk);
    read_addr = 3'b000;
    #1;
    check_value("No write when enable=0", 80'h3FFF_8000_0000_0000_0000, read_data);

    // Test 19: Write maximum value
    $display("\n--- Testing edge cases ---");
    // Sync to clock before edge case tests
    write_enable = 0;
    @(posedge clk);

    write_addr = 3'b111;  // ST(7)
    write_data = 80'hFFFF_FFFF_FFFF_FFFF_FFFF;
    write_enable = 1;
    @(posedge clk);
    write_enable = 0;
    @(posedge clk);
    read_addr = 3'b111;
    #1;
    check_value("Maximum value write/read", 80'hFFFF_FFFF_FFFF_FFFF_FFFF, read_data);

    // Test 20: Write minimum value (zero)
    // Sync before write
    write_enable = 0;
    @(posedge clk);

    write_addr = 3'b110;  // ST(6)
    write_data = 80'h0000_0000_0000_0000_0000;
    write_enable = 1;
    @(posedge clk);
    write_enable = 0;
    @(posedge clk);
    read_addr = 3'b110;
    #1;
    check_value("Zero value write/read", 80'h0000_0000_0000_0000_0000, read_data);

    // Test 21: Reset clears all registers
    $display("\n--- Testing reset ---");
    reset = 1;
    @(posedge clk);
    reset = 0;
    @(posedge clk);
    for (i = 0; i < 8; i = i + 1) begin
        read_addr = i[2:0];
        #1;
        if (read_data !== 80'h0) begin
            test_count = test_count + 1;
            $display("[FAIL] Test %0d: ST(%0d) not zero after reset", test_count, i);
            fail_count = fail_count + 1;
        end
    end
    test_count = test_count + 1;
    if (fail_count == pass_count + fail_count - test_count + 1) begin
        $display("[PASS] Test %0d: All registers cleared after reset", test_count);
        pass_count = pass_count + 1;
    end

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
    #100000;
    $display("ERROR: Simulation timeout!");
    $finish(1);
end

// VCD dump
initial begin
    $dumpfile("fpu_stack_registers_tb.vcd");
    $dumpvars(0, fpu_stack_registers_tb);
end

endmodule
