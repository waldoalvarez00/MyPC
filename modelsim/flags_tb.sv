// ================================================================
// Unit Test for Flags Module
// Tests CPU flags register (C, P, A, Z, S, T, I, D, O)
// ================================================================

`timescale 1ns/1ps

module flags_tb;

    // Include flag definitions
    `include "../Quartus/rtl/CPU/FlagsEnum.sv"

    // DUT signals
    logic clk;
    logic reset;
    logic [15:0] flags_in;
    logic [8:0] update_flags;
    logic [15:0] flags_out;

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Instantiate DUT
    Flags dut (
        .clk(clk),
        .reset(reset),
        .flags_in(flags_in),
        .update_flags(update_flags),
        .flags_out(flags_out)
    );

    // Clock generation: 50 MHz
    initial begin
        clk = 0;
        forever #10 clk = ~clk;
    end

    task check_result(input string test_name, input logic condition);
        test_count++;
        if (condition) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s", test_count, test_name);
            $display("        Expected condition to be true, but was false");
            $display("        flags_out = 0x%04h", flags_out);
            fail_count++;
        end
    endtask

    // Helper to check specific flag
    task check_flag(input string flag_name, input int flag_idx, input logic expected);
        logic actual = flags_out[flag_idx];
        test_count++;
        if (actual == expected) begin
            $display("[PASS] Test %0d: %s = %b", test_count, flag_name, expected);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s (expected %b, got %b)",
                     test_count, flag_name, expected, actual);
            fail_count++;
        end
    endtask

    // Main test sequence
    initial begin
        $display("================================================================");
        $display("Flags Module Unit Test");
        $display("================================================================\n");

        // Initialize
        reset = 1;
        flags_in = 0;
        update_flags = 0;

        repeat(3) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        // ================================================================
        // TEST 1: Reset State
        // ================================================================
        $display("--- Test 1: Reset State ---");

        check_flag("CF after reset", CF_IDX, 0);
        check_flag("PF after reset", PF_IDX, 0);
        check_flag("AF after reset", AF_IDX, 0);
        check_flag("ZF after reset", ZF_IDX, 0);
        check_flag("SF after reset", SF_IDX, 0);
        check_flag("TF after reset", TF_IDX, 0);
        check_flag("IF after reset", IF_IDX, 0);
        check_flag("DF after reset", DF_IDX, 0);
        check_flag("OF after reset", OF_IDX, 0);

        // ================================================================
        // TEST 2: Set Carry Flag
        // ================================================================
        $display("\n--- Test 2: Set Carry Flag ---");

        flags_in = 16'b0;
        flags_in[CF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_CF);
        @(posedge clk);
        @(posedge clk);

        check_flag("CF set", CF_IDX, 1);
        check_flag("Other flags unchanged (PF)", PF_IDX, 0);

        // ================================================================
        // TEST 3: Set Zero Flag
        // ================================================================
        $display("\n--- Test 3: Set Zero Flag ---");

        flags_in = 16'b0;
        flags_in[ZF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_ZF);
        @(posedge clk);
        @(posedge clk);

        check_flag("ZF set", ZF_IDX, 1);
        check_flag("CF still set from previous test", CF_IDX, 1);

        // ================================================================
        // TEST 4: Set Sign Flag
        // ================================================================
        $display("\n--- Test 4: Set Sign Flag ---");

        flags_in = 16'b0;
        flags_in[SF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_SF);
        @(posedge clk);
        @(posedge clk);

        check_flag("SF set", SF_IDX, 1);

        // ================================================================
        // TEST 5: Set Overflow Flag
        // ================================================================
        $display("\n--- Test 5: Set Overflow Flag ---");

        flags_in = 16'b0;
        flags_in[OF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_OF);
        @(posedge clk);
        @(posedge clk);

        check_flag("OF set", OF_IDX, 1);

        // ================================================================
        // TEST 6: Set Parity Flag
        // ================================================================
        $display("\n--- Test 6: Set Parity Flag ---");

        flags_in = 16'b0;
        flags_in[PF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_PF);
        @(posedge clk);
        @(posedge clk);

        check_flag("PF set", PF_IDX, 1);

        // ================================================================
        // TEST 7: Set Auxiliary Carry Flag
        // ================================================================
        $display("\n--- Test 7: Set Auxiliary Carry ---");

        flags_in = 16'b0;
        flags_in[AF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_AF);
        @(posedge clk);
        @(posedge clk);

        check_flag("AF set", AF_IDX, 1);

        // ================================================================
        // TEST 8: Set Trap Flag (for single-step debugging)
        // ================================================================
        $display("\n--- Test 8: Set Trap Flag ---");

        flags_in = 16'b0;
        flags_in[TF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_TF);
        @(posedge clk);
        @(posedge clk);

        check_flag("TF set", TF_IDX, 1);

        // ================================================================
        // TEST 9: Set Interrupt Enable Flag
        // ================================================================
        $display("\n--- Test 9: Set Interrupt Enable ---");

        flags_in = 16'b0;
        flags_in[IF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_IF);
        @(posedge clk);
        @(posedge clk);

        check_flag("IF set", IF_IDX, 1);

        // ================================================================
        // TEST 10: Set Direction Flag
        // ================================================================
        $display("\n--- Test 10: Set Direction Flag ---");

        flags_in = 16'b0;
        flags_in[DF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_DF);
        @(posedge clk);
        @(posedge clk);

        check_flag("DF set", DF_IDX, 1);

        // ================================================================
        // TEST 11: Clear Flags
        // ================================================================
        $display("\n--- Test 11: Clear Flags ---");

        flags_in = 16'b0;  // All zeros
        update_flags = (1 << UpdateFlags_CF) | (1 << UpdateFlags_ZF) |
                       (1 << UpdateFlags_SF);
        @(posedge clk);
        @(posedge clk);

        check_flag("CF cleared", CF_IDX, 0);
        check_flag("ZF cleared", ZF_IDX, 0);
        check_flag("SF cleared", SF_IDX, 0);

        // ================================================================
        // TEST 12: Update Multiple Flags Simultaneously
        // ================================================================
        $display("\n--- Test 12: Multiple Flag Update ---");

        flags_in = 16'b0;
        flags_in[CF_IDX] = 1'b1;
        flags_in[ZF_IDX] = 1'b1;
        flags_in[OF_IDX] = 1'b1;
        flags_in[SF_IDX] = 1'b1;
        update_flags = (1 << UpdateFlags_CF) | (1 << UpdateFlags_ZF) |
                       (1 << UpdateFlags_OF) | (1 << UpdateFlags_SF);
        @(posedge clk);
        @(posedge clk);

        check_flag("CF in multi-update", CF_IDX, 1);
        check_flag("ZF in multi-update", ZF_IDX, 1);
        check_flag("OF in multi-update", OF_IDX, 1);
        check_flag("SF in multi-update", SF_IDX, 1);

        // ================================================================
        // TEST 13: Selective Flag Preservation
        // ================================================================
        $display("\n--- Test 13: Selective Preservation ---");

        // Set all flags
        flags_in = 16'hFFFF;
        update_flags = 9'h1FF;  // Update all
        @(posedge clk);
        @(posedge clk);

        // Now update only CF, others should be preserved
        flags_in = 16'b0;  // Try to clear all
        flags_in[CF_IDX] = 1'b0;
        update_flags = (1 << UpdateFlags_CF);  // Only update CF
        @(posedge clk);
        @(posedge clk);

        check_flag("CF updated to 0", CF_IDX, 0);
        check_flag("ZF preserved as 1", ZF_IDX, 1);
        check_flag("SF preserved as 1", SF_IDX, 1);
        check_flag("OF preserved as 1", OF_IDX, 1);

        // ================================================================
        // TEST 14: No Update When update_flags is 0
        // ================================================================
        $display("\n--- Test 14: No Update ---");

        logic [15:0] before_flags = flags_out;
        flags_in = 16'b0;  // Try to clear all
        update_flags = 9'b0;  // But don't update anything
        @(posedge clk);
        @(posedge clk);

        check_result("Flags unchanged when update=0", flags_out == before_flags);

        // ================================================================
        // TEST 15: Flag Format (x86 compatibility)
        // ================================================================
        $display("\n--- Test 15: Flag Format ---");

        // Set all flags to 1
        flags_in = 16'hFFFF;
        update_flags = 9'h1FF;
        @(posedge clk);
        @(posedge clk);

        // Check format: {4'b0000, O, D, I, T, S, Z, 1'b0, A, 1'b0, P, 1'b1, C}
        check_result("Bit 1 always 1 (reserved)", flags_out[1] == 1'b1);
        check_result("Bit 3 always 0 (reserved)", flags_out[3] == 1'b0);
        check_result("Bit 5 always 0 (reserved)", flags_out[5] == 1'b0);

        // ================================================================
        // Summary
        // ================================================================
        $display("\n================================================================");
        $display("TEST SUMMARY");
        $display("================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %0d%%", (pass_count * 100) / test_count);
        $display("================================================================");

        if (fail_count == 0) begin
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓\n");
            $finish(0);
        end else begin
            $display("✗✗✗ SOME TESTS FAILED ✗✗✗\n");
            $finish(1);
        end
    end

endmodule
