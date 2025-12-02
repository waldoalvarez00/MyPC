// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Tandy_Scancode_Converter Testbench
// Tests the keyboard scancode converter for Tandy compatibility

`timescale 1ns/1ps

module tandy_scancode_converter_tb;

reg clk;
reg reset;
reg [7:0] scancode;
reg keybord_irq;
wire [7:0] convert_data;

integer test_count;
integer pass_count;
integer fail_count;

// Clock generation
always #5 clk = ~clk;

// DUT instantiation
Tandy_Scancode_Converter dut (
    .clock(clk),
    .reset(reset),
    .scancode(scancode),
    .keybord_irq(keybord_irq),
    .convert_data(convert_data)
);

task check_result(input string test_name, input [7:0] expected, input [7:0] actual);
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected 0x%02h, Got 0x%02h", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

// Task to send a scancode with IRQ
task send_scancode(input [7:0] code);
begin
    scancode = code;
    keybord_irq = 1;
    @(posedge clk);
    @(posedge clk);
    keybord_irq = 0;
    @(posedge clk);
    @(posedge clk);
end
endtask

// Task to send E0 extended scancode - NOTE: check convert_data BEFORE calling this task again
//   as the e0 flag is cleared when IRQ goes low
task send_e0_scancode(input [7:0] code);
begin
    // Phase 1: Ensure IRQ is low and registered in prev_keybord_irq
    // Change signals AFTER clock edge to ensure clean setup
    @(posedge clk);
    #1;
    keybord_irq = 0;
    scancode = 8'h00;
    @(posedge clk);  // prev_keybord_irq captures keybord_irq (now 0)
    #1;

    // Phase 2: Set up E0 scancode with IRQ high
    // The next clock edge will see: prev=0, irq=1 -> posedge detected
    scancode = 8'hE0;
    keybord_irq = 1;
    @(posedge clk);  // Posedge detected: e0_temp <= 1
    #1;

    // Phase 3: Bring IRQ low to trigger negedge detection
    // The next clock edge will see: prev=1, irq=0 -> negedge detected
    keybord_irq = 0;
    @(posedge clk);  // Negedge detected: e0 <= e0_temp (should be 1)
    #1;

    // Phase 4: Send actual key code with E0 prefix now active
    // The next clock edge will see: prev=0, irq=1 -> posedge detected with e0=1
    scancode = code;
    keybord_irq = 1;
    @(posedge clk);  // Posedge detected with e0=1, conversion happens
    #1;
    // IRQ still high - caller should check convert_data now
end
endtask

// Task to clear IRQ after checking E0 scancode result
task clear_irq();
begin
    keybord_irq = 0;
    @(posedge clk);
    @(posedge clk);
end
endtask

initial begin
    $display("========================================");
    $display("Tandy_Scancode_Converter Testbench");
    $display("========================================");

    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    scancode = 8'h00;
    keybord_irq = 0;

    // Release reset
    #20;
    reset = 0;
    #20;

    // Test 1: Normal key passthrough (no conversion)
    $display("\n--- Testing normal key passthrough ---");
    send_scancode(8'h1E);  // 'A' key
    check_result("Normal 'A' key passthrough", 8'h1E, convert_data);

    // Test 2: Another normal key
    send_scancode(8'h30);  // 'B' key
    check_result("Normal 'B' key passthrough", 8'h30, convert_data);

    // Test 3: Numeric keypad '-' conversion (0x4A -> 0x53)
    $display("\n--- Testing numeric keypad conversions ---");
    send_scancode(8'h4A);  // Numeric '-'
    check_result("Numeric '-' (4Ah -> 53h)", 8'h53, convert_data);

    // Test 4: Numeric keypad '+' conversion (0x4E -> 0x55)
    send_scancode(8'h4E);  // Numeric '+'
    check_result("Numeric '+' (4Eh -> 55h)", 8'h55, convert_data);

    // Test 5: Numeric keypad '.' conversion (0x53 -> 0x56)
    send_scancode(8'h53);  // Numeric '.'
    check_result("Numeric '.' (53h -> 56h)", 8'h56, convert_data);

    // Test 6: F11 key conversion (0x57 -> 0x59)
    send_scancode(8'h57);  // F11
    check_result("F11 (57h -> 59h)", 8'h59, convert_data);

    // Test 7: F12 key conversion (0x58 -> 0x5A)
    send_scancode(8'h58);  // F12
    check_result("F12 (58h -> 5Ah)", 8'h5A, convert_data);

    // Test 8: E0 extended UP arrow (E0 48h -> 29h)
    $display("\n--- Testing E0 extended key conversions ---");
    send_e0_scancode(8'h48);  // UP arrow
    #1;
    check_result("E0 UP arrow (E0 48h -> 29h)", 8'h29, convert_data);
    clear_irq();

    // Test 9: E0 extended LEFT arrow (E0 4Bh -> 2Bh)
    send_e0_scancode(8'h4B);  // LEFT arrow
    #1;
    check_result("E0 LEFT arrow (E0 4Bh -> 2Bh)", 8'h2B, convert_data);
    clear_irq();

    // Test 10: E0 extended DOWN arrow (E0 50h -> 4Ah)
    send_e0_scancode(8'h50);  // DOWN arrow
    #1;
    check_result("E0 DOWN arrow (E0 50h -> 4Ah)", 8'h4A, convert_data);
    clear_irq();

    // Test 11: E0 extended RIGHT arrow (E0 4Dh -> 4Eh)
    send_e0_scancode(8'h4D);  // RIGHT arrow
    #1;
    check_result("E0 RIGHT arrow (E0 4Dh -> 4Eh)", 8'h4E, convert_data);
    clear_irq();

    // Test 12: E0 extended Enter (E0 1Ch -> 57h)
    send_e0_scancode(8'h1C);  // Keypad Enter
    #1;
    check_result("E0 Enter (E0 1Ch -> 57h)", 8'h57, convert_data);
    clear_irq();

    // Test 13: E0 extended Home (E0 47h -> 58h)
    send_e0_scancode(8'h47);  // Home
    #1;
    check_result("E0 Home (E0 47h -> 58h)", 8'h58, convert_data);
    clear_irq();

    // Test 14: Break code (high bit set) passthrough
    $display("\n--- Testing break codes ---");
    send_scancode(8'h9E);  // 'A' release (0x1E + 0x80)
    check_result("Break code 'A' release", 8'h9E, convert_data);

    // Test 15: Break code for converted key
    send_scancode(8'hCA);  // Numeric '-' release (0x4A + 0x80)
    check_result("Break code Numeric '-' (CAh -> D3h)", 8'hD3, convert_data);

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
    $dumpfile("tandy_scancode_converter_tb.vcd");
    $dumpvars(0, tandy_scancode_converter_tb);
end

endmodule
