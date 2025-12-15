`timescale 1ns/1ps

module JumpTest_tb;

// Include flag definitions
parameter CF_IDX = 0;  // Carry Flag
parameter PF_IDX = 2;  // Parity Flag
parameter ZF_IDX = 6;  // Zero Flag
parameter SF_IDX = 7;  // Sign Flag
parameter OF_IDX = 11; // Overflow Flag

// Testbench signals
logic [7:0] opcode;
logic [15:0] flags;
logic taken;

// Test statistics
integer test_count = 0;
integer pass_count = 0;
integer fail_count = 0;

// Instantiate the JumpTest module
JumpTest uut (
    .opcode(opcode),
    .flags(flags),
    .taken(taken)
);

// Test task
task automatic check_jump(input string test_name, input logic [7:0] op,
                          input logic [15:0] flg, input logic expected);
    opcode = op;
    flags = flg;
    #1;  // Wait for combinational logic
    test_count++;
    if (taken === expected) begin
        $display("[PASS] %s: opcode=0x%02h, flags=0x%04h, taken=%b",
                 test_name, op, flg, taken);
        pass_count++;
    end else begin
        $display("[FAIL] %s: opcode=0x%02h, flags=0x%04h, expected=%b, got=%b",
                 test_name, op, flg, expected, taken);
        fail_count++;
    end
endtask

// Helper function to set specific flag
function logic [15:0] set_flag(input logic [15:0] base_flags, input integer flag_idx, input logic value);
    if (value)
        return base_flags | (1 << flag_idx);
    else
        return base_flags & ~(1 << flag_idx);
endfunction

// Main test sequence
initial begin
    $display("========================================");
    $display("JumpTest Testbench Started");
    $display("========================================");

    // Initialize signals
    opcode = 8'h00;
    flags = 16'h0000;
    #10;

    //========================================
    // TEST 1: JO (Jump if Overflow) - 0x70
    //========================================
    $display("\n--- TEST 1: JO (0x70) - Jump if Overflow ---");
    check_jump("JO with OF=1", 8'h70, set_flag(16'h0000, OF_IDX, 1), 1'b1);
    check_jump("JO with OF=0", 8'h70, set_flag(16'h0000, OF_IDX, 0), 1'b0);

    //========================================
    // TEST 2: JNO (Jump if Not Overflow) - 0x71
    //========================================
    $display("\n--- TEST 2: JNO (0x71) - Jump if Not Overflow ---");
    check_jump("JNO with OF=0", 8'h71, set_flag(16'h0000, OF_IDX, 0), 1'b1);
    check_jump("JNO with OF=1", 8'h71, set_flag(16'h0000, OF_IDX, 1), 1'b0);

    //========================================
    // TEST 3: JB/JC (Jump if Below/Carry) - 0x72
    //========================================
    $display("\n--- TEST 3: JB/JC (0x72) - Jump if Below/Carry ---");
    check_jump("JB with CF=1", 8'h72, set_flag(16'h0000, CF_IDX, 1), 1'b1);
    check_jump("JB with CF=0", 8'h72, set_flag(16'h0000, CF_IDX, 0), 1'b0);

    //========================================
    // TEST 4: JNB/JNC (Jump if Not Below/Carry) - 0x73
    //========================================
    $display("\n--- TEST 4: JNB/JNC (0x73) - Jump if Not Below/Carry ---");
    check_jump("JNB with CF=0", 8'h73, set_flag(16'h0000, CF_IDX, 0), 1'b1);
    check_jump("JNB with CF=1", 8'h73, set_flag(16'h0000, CF_IDX, 1), 1'b0);

    //========================================
    // TEST 5: JE/JZ (Jump if Equal/Zero) - 0x74
    //========================================
    $display("\n--- TEST 5: JE/JZ (0x74) - Jump if Equal/Zero ---");
    check_jump("JE with ZF=1", 8'h74, set_flag(16'h0000, ZF_IDX, 1), 1'b1);
    check_jump("JE with ZF=0", 8'h74, set_flag(16'h0000, ZF_IDX, 0), 1'b0);

    //========================================
    // TEST 6: JNE/JNZ (Jump if Not Equal/Zero) - 0x75
    //========================================
    $display("\n--- TEST 6: JNE/JNZ (0x75) - Jump if Not Equal/Zero ---");
    check_jump("JNE with ZF=0", 8'h75, set_flag(16'h0000, ZF_IDX, 0), 1'b1);
    check_jump("JNE with ZF=1", 8'h75, set_flag(16'h0000, ZF_IDX, 1), 1'b0);

    //========================================
    // TEST 7: JBE (Jump if Below or Equal) - 0x76
    //========================================
    $display("\n--- TEST 7: JBE (0x76) - Jump if Below or Equal ---");
    check_jump("JBE with CF=1 ZF=0", 8'h76,
               set_flag(set_flag(16'h0000, CF_IDX, 1), ZF_IDX, 0), 1'b1);
    check_jump("JBE with CF=0 ZF=1", 8'h76,
               set_flag(set_flag(16'h0000, CF_IDX, 0), ZF_IDX, 1), 1'b1);
    check_jump("JBE with CF=1 ZF=1", 8'h76,
               set_flag(set_flag(16'h0000, CF_IDX, 1), ZF_IDX, 1), 1'b1);
    check_jump("JBE with CF=0 ZF=0", 8'h76,
               set_flag(set_flag(16'h0000, CF_IDX, 0), ZF_IDX, 0), 1'b0);

    //========================================
    // TEST 8: JNBE/JA (Jump if Not Below or Equal) - 0x77
    //========================================
    $display("\n--- TEST 8: JNBE/JA (0x77) - Jump if Above ---");
    check_jump("JA with CF=0 ZF=0", 8'h77,
               set_flag(set_flag(16'h0000, CF_IDX, 0), ZF_IDX, 0), 1'b1);
    check_jump("JA with CF=1 ZF=0", 8'h77,
               set_flag(set_flag(16'h0000, CF_IDX, 1), ZF_IDX, 0), 1'b0);
    check_jump("JA with CF=0 ZF=1", 8'h77,
               set_flag(set_flag(16'h0000, CF_IDX, 0), ZF_IDX, 1), 1'b0);

    //========================================
    // TEST 9: JS (Jump if Sign) - 0x78
    //========================================
    $display("\n--- TEST 9: JS (0x78) - Jump if Sign ---");
    check_jump("JS with SF=1", 8'h78, set_flag(16'h0000, SF_IDX, 1), 1'b1);
    check_jump("JS with SF=0", 8'h78, set_flag(16'h0000, SF_IDX, 0), 1'b0);

    //========================================
    // TEST 10: JNS (Jump if Not Sign) - 0x79
    //========================================
    $display("\n--- TEST 10: JNS (0x79) - Jump if Not Sign ---");
    check_jump("JNS with SF=0", 8'h79, set_flag(16'h0000, SF_IDX, 0), 1'b1);
    check_jump("JNS with SF=1", 8'h79, set_flag(16'h0000, SF_IDX, 1), 1'b0);

    //========================================
    // TEST 11: JP/JPE (Jump if Parity) - 0x7A
    //========================================
    $display("\n--- TEST 11: JP/JPE (0x7A) - Jump if Parity ---");
    check_jump("JP with PF=1", 8'h7A, set_flag(16'h0000, PF_IDX, 1), 1'b1);
    check_jump("JP with PF=0", 8'h7A, set_flag(16'h0000, PF_IDX, 0), 1'b0);

    //========================================
    // TEST 12: JNP/JPO (Jump if Not Parity) - 0x7B
    //========================================
    $display("\n--- TEST 12: JNP/JPO (0x7B) - Jump if Not Parity ---");
    check_jump("JNP with PF=0", 8'h7B, set_flag(16'h0000, PF_IDX, 0), 1'b1);
    check_jump("JNP with PF=1", 8'h7B, set_flag(16'h0000, PF_IDX, 1), 1'b0);

    //========================================
    // TEST 13: JL/JNGE (Jump if Less) - 0x7C
    //========================================
    $display("\n--- TEST 13: JL/JNGE (0x7C) - Jump if Less ---");
    check_jump("JL with SF=1 OF=0", 8'h7C,
               set_flag(set_flag(16'h0000, SF_IDX, 1), OF_IDX, 0), 1'b1);
    check_jump("JL with SF=0 OF=1", 8'h7C,
               set_flag(set_flag(16'h0000, SF_IDX, 0), OF_IDX, 1), 1'b1);
    check_jump("JL with SF=0 OF=0", 8'h7C,
               set_flag(set_flag(16'h0000, SF_IDX, 0), OF_IDX, 0), 1'b0);
    check_jump("JL with SF=1 OF=1", 8'h7C,
               set_flag(set_flag(16'h0000, SF_IDX, 1), OF_IDX, 1), 1'b0);

    //========================================
    // TEST 14: JNL/JGE (Jump if Not Less) - 0x7D
    //========================================
    $display("\n--- TEST 14: JNL/JGE (0x7D) - Jump if Greater or Equal ---");
    check_jump("JGE with SF=0 OF=0", 8'h7D,
               set_flag(set_flag(16'h0000, SF_IDX, 0), OF_IDX, 0), 1'b1);
    check_jump("JGE with SF=1 OF=1", 8'h7D,
               set_flag(set_flag(16'h0000, SF_IDX, 1), OF_IDX, 1), 1'b1);
    check_jump("JGE with SF=1 OF=0", 8'h7D,
               set_flag(set_flag(16'h0000, SF_IDX, 1), OF_IDX, 0), 1'b0);

    //========================================
    // TEST 15: JLE/JNG (Jump if Less or Equal) - 0x7E
    //========================================
    $display("\n--- TEST 15: JLE/JNG (0x7E) - Jump if Less or Equal ---");
    check_jump("JLE with SF=1 OF=0 ZF=0", 8'h7E,
               set_flag(set_flag(set_flag(16'h0000, SF_IDX, 1), OF_IDX, 0), ZF_IDX, 0), 1'b1);
    check_jump("JLE with SF=0 OF=0 ZF=1", 8'h7E,
               set_flag(set_flag(set_flag(16'h0000, SF_IDX, 0), OF_IDX, 0), ZF_IDX, 1), 1'b1);
    check_jump("JLE with SF=0 OF=0 ZF=0", 8'h7E,
               set_flag(set_flag(set_flag(16'h0000, SF_IDX, 0), OF_IDX, 0), ZF_IDX, 0), 1'b0);

    //========================================
    // TEST 16: JNLE/JG (Jump if Greater) - 0x7F
    //========================================
    $display("\n--- TEST 16: JNLE/JG (0x7F) - Jump if Greater ---");
    check_jump("JG with SF=0 OF=0 ZF=0", 8'h7F,
               set_flag(set_flag(set_flag(16'h0000, SF_IDX, 0), OF_IDX, 0), ZF_IDX, 0), 1'b1);
    check_jump("JG with SF=1 OF=1 ZF=0", 8'h7F,
               set_flag(set_flag(set_flag(16'h0000, SF_IDX, 1), OF_IDX, 1), ZF_IDX, 0), 1'b1);
    check_jump("JG with SF=0 OF=0 ZF=1", 8'h7F,
               set_flag(set_flag(set_flag(16'h0000, SF_IDX, 0), OF_IDX, 0), ZF_IDX, 1), 1'b0);

    //========================================
    // TEST 17: BOUND - 0x62
    //========================================
    $display("\n--- TEST 17: BOUND (0x62) ---");
    check_jump("BOUND with CF=1", 8'h62, set_flag(16'h0000, CF_IDX, 1), 1'b1);
    check_jump("BOUND with CF=0", 8'h62, set_flag(16'h0000, CF_IDX, 0), 1'b0);

    //========================================
    // TEST 18: INTO - 0xCE
    //========================================
    $display("\n--- TEST 18: INTO (0xCE) ---");
    check_jump("INTO with OF=1", 8'hCE, set_flag(16'h0000, OF_IDX, 1), 1'b1);
    check_jump("INTO with OF=0", 8'hCE, set_flag(16'h0000, OF_IDX, 0), 1'b0);

    //========================================
    // TEST 19: Unknown Opcodes (should not take jump)
    //========================================
    $display("\n--- TEST 19: Unknown Opcodes ---");
    check_jump("Unknown opcode 0x00", 8'h00, 16'hFFFF, 1'b0);
    check_jump("Unknown opcode 0xFF", 8'hFF, 16'hFFFF, 1'b0);

    //========================================
    // Test Summary
    //========================================
    #10;
    $display("\n========================================");
    $display("JumpTest Testbench Complete");
    $display("========================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    if (fail_count == 0)
        $display("STATUS: ALL TESTS PASSED!");
    else
        $display("STATUS: SOME TESTS FAILED!");
    $display("========================================");

    $finish;
end

endmodule
