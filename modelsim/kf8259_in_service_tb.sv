// ================================================================
// Unit Test for KF8259_In_Service
// Tests in-service register management and EOI handling
// ================================================================

`timescale 1ns/1ps
`include "KF8259_Common_Package.svh"

module kf8259_in_service_tb;

    // DUT signals
    logic clock;
    logic reset;
    logic [2:0] priority_rotate;
    logic [7:0] interrupt_special_mask;
    logic [7:0] interrupt;
    logic latch_in_service;
    logic [7:0] end_of_interrupt;
    logic [7:0] in_service_register;
    logic [7:0] highest_level_in_service;

    // Instantiate DUT
    KF8259_In_Service dut (
        .clock(clock),
        .reset(reset),
        .priority_rotate(priority_rotate),
        .interrupt_special_mask(interrupt_special_mask),
        .interrupt(interrupt),
        .latch_in_service(latch_in_service),
        .end_of_interrupt(end_of_interrupt),
        .in_service_register(in_service_register),
        .highest_level_in_service(highest_level_in_service)
    );

    // Clock generation
    initial begin
        clock = 0;
        forever #10 clock = ~clock;
    end

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

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
        $display("KF8259_In_Service Unit Test");
        $display("================================================================");

        // Initialize
        reset = 1;
        priority_rotate = 3'b111;  // No rotation
        interrupt_special_mask = 8'h00;
        interrupt = 8'h00;
        latch_in_service = 0;
        end_of_interrupt = 8'h00;

        repeat(5) @(posedge clock);
        reset = 0;
        repeat(2) @(posedge clock);

        // ================================================================
        // TEST 1: Single Interrupt Latching
        // ================================================================
        $display("\n--- Test 1: Single Interrupt Latching (IRQ0) ---");

        interrupt = 8'b00000001;  // IRQ0
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("IRQ0 latched in ISR", in_service_register == 8'b00000001);
        check_result("Highest level = IRQ0", highest_level_in_service == 8'b00000001);

        // ================================================================
        // TEST 2: EOI Clears In-Service
        // ================================================================
        $display("\n--- Test 2: EOI Clears In-Service ---");

        end_of_interrupt = 8'b00000001;  // EOI for IRQ0
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        check_result("EOI clears IRQ0 from ISR", in_service_register == 8'h00);
        check_result("Highest level cleared", highest_level_in_service == 8'h00);

        // ================================================================
        // TEST 3: Multiple Interrupts in Service
        // ================================================================
        $display("\n--- Test 3: Multiple Interrupts in Service ---");

        // Latch IRQ2
        interrupt = 8'b00000100;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("IRQ2 in service", in_service_register[2] == 1'b1);

        // Latch IRQ5 (while IRQ2 still in service)
        interrupt = 8'b00100000;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("IRQ2 and IRQ5 both in service",
                     in_service_register == 8'b00100100);
        check_result("Highest level = IRQ2 (higher priority)",
                     highest_level_in_service == 8'b00000100);

        // ================================================================
        // TEST 4: Selective EOI
        // ================================================================
        $display("\n--- Test 4: Selective EOI ---");

        // EOI for IRQ5 only
        end_of_interrupt = 8'b00100000;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        check_result("IRQ5 cleared, IRQ2 remains",
                     in_service_register == 8'b00000100);
        check_result("Highest level still IRQ2",
                     highest_level_in_service == 8'b00000100);

        // Clear IRQ2
        end_of_interrupt = 8'b00000100;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        check_result("All cleared", in_service_register == 8'h00);

        // ================================================================
        // TEST 5: All IRQs in Service
        // ================================================================
        $display("\n--- Test 5: All IRQs in Service ---");

        // Latch all 8 IRQs
        interrupt = 8'hFF;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("All IRQs in service", in_service_register == 8'hFF);
        check_result("Highest level = IRQ0 (highest priority)",
                     highest_level_in_service == 8'b00000001);

        // Clear all
        end_of_interrupt = 8'hFF;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        check_result("All EOI clears all ISR", in_service_register == 8'h00);

        // ================================================================
        // TEST 6: Priority Rotation Effect on Highest Level
        // ================================================================
        $display("\n--- Test 6: Priority Rotation Effect ---");

        // Latch IRQ0, IRQ4
        interrupt = 8'b00010001;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("IRQ0 and IRQ4 in service",
                     in_service_register == 8'b00010001);

        // Without rotation, IRQ0 has highest priority
        priority_rotate = 3'b111;
        @(posedge clock);
        check_result("No rotation: IRQ0 is highest",
                     highest_level_in_service == 8'b00000001);

        // With rotation by 4, IRQ4 becomes higher priority than IRQ0
        priority_rotate = 3'b011;
        @(posedge clock);
        check_result("Rotation by 4: IRQ4 becomes highest",
                     highest_level_in_service == 8'b00010000);

        // Clear all
        priority_rotate = 3'b111;
        end_of_interrupt = 8'hFF;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        // ================================================================
        // TEST 7: Special Mask Effect
        // ================================================================
        $display("\n--- Test 7: Special Mask Effect ---");

        // Latch IRQ1, IRQ3, IRQ5
        interrupt = 8'b00101010;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("IRQ1, 3, 5 in service",
                     in_service_register == 8'b00101010);

        // Special mask IRQ1
        interrupt_special_mask = 8'b00000010;
        @(posedge clock);

        // Highest should now be IRQ3 (IRQ1 is masked)
        check_result("Special mask affects highest level",
                     highest_level_in_service == 8'b00001000);

        // Clear special mask
        interrupt_special_mask = 8'h00;
        end_of_interrupt = 8'hFF;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        // ================================================================
        // TEST 8: Nested Interrupt Sequence
        // ================================================================
        $display("\n--- Test 8: Nested Interrupt Sequence ---");

        // Service IRQ7 (low priority)
        interrupt = 8'b10000000;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("IRQ7 in service", in_service_register[7] == 1'b1);

        // Interrupt with IRQ0 (high priority)
        interrupt = 8'b00000001;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        check_result("Both IRQ0 and IRQ7 in service",
                     in_service_register == 8'b10000001);
        check_result("Highest is IRQ0",
                     highest_level_in_service == 8'b00000001);

        // EOI IRQ0
        end_of_interrupt = 8'b00000001;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        check_result("IRQ7 still in service after IRQ0 EOI",
                     in_service_register == 8'b10000000);
        check_result("Highest is now IRQ7",
                     highest_level_in_service == 8'b10000000);

        // Clear all
        end_of_interrupt = 8'hFF;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        // ================================================================
        // TEST 9: Simultaneous Latch and EOI
        // ================================================================
        $display("\n--- Test 9: Simultaneous Latch and EOI ---");

        // Latch IRQ2
        interrupt = 8'b00000100;
        latch_in_service = 1;
        end_of_interrupt = 8'b00000100;  // Simultaneous EOI
        @(posedge clock);
        latch_in_service = 0;
        end_of_interrupt = 8'h00;
        @(posedge clock);

        // Should be cleared by EOI immediately
        check_result("Simultaneous latch and EOI results in clear",
                     in_service_register == 8'h00);

        // ================================================================
        // TEST 10: Reset Behavior
        // ================================================================
        $display("\n--- Test 10: Reset Behavior ---");

        // Set some ISR bits
        interrupt = 8'b01010101;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        // Assert reset
        reset = 1;
        @(posedge clock);
        reset = 0;
        @(posedge clock);

        check_result("Reset clears ISR", in_service_register == 8'h00);
        check_result("Reset clears highest level", highest_level_in_service == 8'h00);

        // ================================================================
        // TEST 11: Rapid Latch/EOI Sequence
        // ================================================================
        $display("\n--- Test 11: Rapid Latch/EOI Sequence ---");

        for (int i = 0; i < 8; i++) begin
            // Latch IRQi
            interrupt = 1 << i;
            latch_in_service = 1;
            @(posedge clock);
            latch_in_service = 0;
            @(posedge clock);

            check_result($sformatf("IRQ%0d latched", i),
                         in_service_register == (1 << i));

            // EOI IRQi
            end_of_interrupt = 1 << i;
            @(posedge clock);
            end_of_interrupt = 8'h00;
            @(posedge clock);

            check_result($sformatf("IRQ%0d cleared", i),
                         in_service_register == 8'h00);
        end

        // ================================================================
        // TEST 12: Multiple Simultaneous EOIs
        // ================================================================
        $display("\n--- Test 12: Multiple Simultaneous EOIs ---");

        // Latch IRQ0, 2, 4, 6
        interrupt = 8'b01010101;
        latch_in_service = 1;
        @(posedge clock);
        latch_in_service = 0;
        @(posedge clock);

        // EOI multiple at once
        end_of_interrupt = 8'b01010000;  // Clear IRQ4, 6
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

        check_result("Multiple EOI clears multiple ISR bits",
                     in_service_register == 8'b00000101);

        // Clear remaining
        end_of_interrupt = 8'hFF;
        @(posedge clock);
        end_of_interrupt = 8'h00;
        @(posedge clock);

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

    // Timeout
    initial begin
        #50000;
        $display("\n[ERROR] Testbench timeout!");
        $finish(1);
    end

endmodule
