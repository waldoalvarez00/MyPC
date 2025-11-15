// ================================================================
// Unit Test for KF8259_Priority_Resolver
// Tests priority resolution, masking, rotation, and special modes
// ================================================================

`timescale 1ns/1ps
`include "KF8259_Common_Package.svh"

module kf8259_priority_resolver_tb;

    // DUT signals
    logic [2:0] priority_rotate;
    logic [7:0] interrupt_mask;
    logic [7:0] interrupt_special_mask;
    logic special_fully_nest_config;
    logic [7:0] highest_level_in_service;
    logic [7:0] interrupt_request_register;
    logic [7:0] in_service_register;
    logic [7:0] interrupt;

    // Instantiate DUT
    KF8259_Priority_Resolver dut (
        .priority_rotate(priority_rotate),
        .interrupt_mask(interrupt_mask),
        .interrupt_special_mask(interrupt_special_mask),
        .special_fully_nest_config(special_fully_nest_config),
        .highest_level_in_service(highest_level_in_service),
        .interrupt_request_register(interrupt_request_register),
        .in_service_register(in_service_register),
        .interrupt(interrupt)
    );

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Local test variables
    logic [7:0] expected_irq;

    task check_result(input string test_name, input logic condition);
        test_count++;
        if (condition) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s", test_count, test_name);
            fail_count++;
        end
    endtask

    // Test sequence
    initial begin
        $display("================================================================");
        $display("KF8259_Priority_Resolver Unit Test");
        $display("================================================================");

        // Initialize
        priority_rotate = 3'b111;  // No rotation
        interrupt_mask = 8'h00;  // All unmasked
        interrupt_special_mask = 8'h00;
        special_fully_nest_config = 1'b0;
        highest_level_in_service = 8'h00;
        interrupt_request_register = 8'h00;
        in_service_register = 8'h00;

        #10;  // Wait for combinational logic

        // ================================================================
        // TEST 1: Single Request - Highest Priority (IRQ0)
        // ================================================================
        $display("\n--- Test 1: Single Request IRQ0 (Highest Priority) ---");

        interrupt_request_register = 8'b00000001;
        in_service_register = 8'h00;
        #10;

        check_result("IRQ0 selected", interrupt == 8'b00000001);

        // ================================================================
        // TEST 2: Single Request - Lowest Priority (IRQ7)
        // ================================================================
        $display("\n--- Test 2: Single Request IRQ7 (Lowest Priority) ---");

        interrupt_request_register = 8'b10000000;
        #10;

        check_result("IRQ7 selected", interrupt == 8'b10000000);

        // ================================================================
        // TEST 3: Multiple Requests - Priority Resolution
        // ================================================================
        $display("\n--- Test 3: Multiple Requests - Priority Resolution ---");

        interrupt_request_register = 8'b10101010;  // IRQ1, 3, 5, 7
        #10;

        check_result("Highest priority IRQ1 selected", interrupt == 8'b00000010);

        interrupt_request_register = 8'b11110000;  // IRQ4, 5, 6, 7
        #10;

        check_result("Highest priority IRQ4 selected", interrupt == 8'b00010000);

        // ================================================================
        // TEST 4: Interrupt Masking
        // ================================================================
        $display("\n--- Test 4: Interrupt Masking ---");

        interrupt_request_register = 8'b00001111;  // IRQ0-3
        interrupt_mask = 8'b00000011;  // Mask IRQ0, IRQ1
        #10;

        check_result("Masked IRQs not selected", interrupt == 8'b00000100);  // IRQ2

        // Reset mask
        interrupt_mask = 8'h00;
        #10;

        // ================================================================
        // TEST 5: In-Service Blocking
        // ================================================================
        $display("\n--- Test 5: In-Service Blocking ---");

        interrupt_request_register = 8'b00000111;  // IRQ0, 1, 2
        in_service_register = 8'b00000001;  // IRQ0 in service
        #10;

        check_result("Higher priority in-service blocks lower", interrupt == 8'b00000000);

        // Clear in-service
        in_service_register = 8'h00;
        #10;

        check_result("No in-service allows interrupt", interrupt == 8'b00000001);

        // ================================================================
        // TEST 6: Equal Priority - Lower Number Wins
        // ================================================================
        $display("\n--- Test 6: Equal Priority In-Service ---");

        interrupt_request_register = 8'b00000110;  // IRQ1, 2
        in_service_register = 8'b00000100;  // IRQ2 in service
        #10;

        check_result("Equal/higher in-service blocks lower priority", interrupt == 8'b00000000);

        interrupt_request_register = 8'b00000010;  // Only IRQ1
        in_service_register = 8'b00000100;  // IRQ2 still in service
        #10;

        check_result("Higher priority allowed even with in-service", interrupt == 8'b00000010);

        in_service_register = 8'h00;
        #10;

        // ================================================================
        // TEST 7: Priority Rotation - Rotate by 1
        // ================================================================
        $display("\n--- Test 7: Priority Rotation - Rotate by 1 ---");

        priority_rotate = 3'b000;  // Rotate by 1 (IRQ1 becomes highest)
        interrupt_request_register = 8'b00000011;  // IRQ0, IRQ1
        in_service_register = 8'h00;
        #10;

        // After rotation by 1, IRQ1 has highest priority
        check_result("After rotation, IRQ1 has priority", interrupt == 8'b00000010);

        // Reset rotation
        priority_rotate = 3'b111;
        #10;

        // ================================================================
        // TEST 8: Priority Rotation - Rotate by 4
        // ================================================================
        $display("\n--- Test 8: Priority Rotation - Rotate by 4 ---");

        priority_rotate = 3'b011;  // Rotate by 4 (IRQ4 becomes highest)
        interrupt_request_register = 8'b00010001;  // IRQ0, IRQ4
        #10;

        // After rotation by 4, IRQ4 has highest priority
        check_result("After rotation by 4, IRQ4 has priority", interrupt == 8'b00010000);

        priority_rotate = 3'b111;
        #10;

        // ================================================================
        // TEST 9: Special Mask Mode
        // ================================================================
        $display("\n--- Test 9: Special Mask Mode ---");

        interrupt_request_register = 8'b00001111;  // IRQ0-3
        interrupt_special_mask = 8'b00000011;  // Special mask IRQ0, IRQ1
        in_service_register = 8'b00000001;  // IRQ0 in service
        #10;

        check_result("Special mask affects in-service blocking", interrupt != 8'b00000000);

        interrupt_special_mask = 8'h00;
        in_service_register = 8'h00;
        #10;

        // ================================================================
        // TEST 10: Special Fully Nested Mode
        // ================================================================
        $display("\n--- Test 10: Special Fully Nested Mode ---");

        special_fully_nest_config = 1'b1;
        highest_level_in_service = 8'b00000100;  // IRQ2
        in_service_register = 8'b00000100;  // IRQ2 in service
        interrupt_request_register = 8'b00000010;  // IRQ1 (higher priority)
        #10;

        check_result("Special fully nested allows higher priority",
                     interrupt == 8'b00000010);

        special_fully_nest_config = 1'b0;
        #10;

        // ================================================================
        // TEST 11: All Requests Masked
        // ================================================================
        $display("\n--- Test 11: All Requests Masked ---");

        interrupt_request_register = 8'hFF;
        interrupt_mask = 8'hFF;  // Mask all
        in_service_register = 8'h00;
        #10;

        check_result("All masked results in no interrupt", interrupt == 8'h00);

        interrupt_mask = 8'h00;
        #10;

        // ================================================================
        // TEST 12: Priority Chain Test
        // ================================================================
        $display("\n--- Test 12: Priority Chain Test ---");

        // Test each priority level sequentially
        for (int i = 0; i < 8; i++) begin
            interrupt_request_register = 8'hFF;  // All pending
            interrupt_mask = ~(8'hFF << i);  // Mask all higher priorities
            in_service_register = 8'h00;
            #10;

            check_result($sformatf("IRQ%0d selected when higher masked", i),
                         interrupt == (1 << i));
        end

        interrupt_mask = 8'h00;
        #10;

        // ================================================================
        // TEST 13: Complex Rotation Scenarios
        // ================================================================
        $display("\n--- Test 13: Complex Rotation Scenarios ---");

        for (int rot = 0; rot < 8; rot++) begin
            priority_rotate = rot[2:0];
            interrupt_request_register = 8'b11111111;
            in_service_register = 8'h00;
            #10;

            // After rotation, the priority should shift
            case (rot)
                0: expected_irq = 8'b00000010;  // IRQ1
                1: expected_irq = 8'b00000100;  // IRQ2
                2: expected_irq = 8'b00001000;  // IRQ3
                3: expected_irq = 8'b00010000;  // IRQ4
                4: expected_irq = 8'b00100000;  // IRQ5
                5: expected_irq = 8'b01000000;  // IRQ6
                6: expected_irq = 8'b10000000;  // IRQ7
                7: expected_irq = 8'b00000001;  // IRQ0
            endcase

            check_result($sformatf("Rotation %0d produces correct priority", rot),
                         interrupt == expected_irq);
        end

        priority_rotate = 3'b111;
        #10;

        // ================================================================
        // TEST 14: No Requests
        // ================================================================
        $display("\n--- Test 14: No Requests ---");

        interrupt_request_register = 8'h00;
        in_service_register = 8'h00;
        #10;

        check_result("No requests results in no interrupt", interrupt == 8'h00);

        // ================================================================
        // TEST 15: Complex In-Service with Multiple Levels
        // ================================================================
        $display("\n--- Test 15: Complex In-Service Scenarios ---");

        interrupt_request_register = 8'b11111111;  // All pending
        in_service_register = 8'b00101000;  // IRQ3, IRQ5 in service
        #10;

        // IRQ0-2 are higher than IRQ3, so they're blocked
        // But actually IRQ0-2 should be allowed since they're higher priority
        // Let me reconsider... In-service blocks LOWER priority, not higher
        check_result("In-service doesn't block higher priority", interrupt != 8'h00);

        // ================================================================
        // Test Summary
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
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓");
            $finish(0);
        end else begin
            $display("✗✗✗ SOME TESTS FAILED ✗✗✗");
            $finish(1);
        end
    end

endmodule
