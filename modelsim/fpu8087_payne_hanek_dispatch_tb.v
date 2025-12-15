// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns/1ps

//=====================================================================
// Testbench for Payne-Hanek Dispatch Logic
//
// Tests the threshold detection and dispatch logic that routes:
// - Small angles (< 100π) to iterative path
// - Large angles (>= 100π) to microcode path
//
// This test uses a mock microcode responder to simulate microcode
// execution without actually implementing the full microcode routine.
//=====================================================================

module tb_payne_hanek_dispatch();

    reg clk;
    reg reset;
    reg enable;
    reg [79:0] angle_in;
    wire [79:0] angle_out;
    wire [1:0] quadrant;
    wire done;
    wire error;

    // Microcode interface
    wire        microcode_invoke;
    wire [11:0] microcode_addr;
    wire [79:0] microcode_operand_a;
    reg         microcode_done;
    reg  [79:0] microcode_result;
    reg  [1:0]  microcode_quadrant;
    reg         microcode_error;

    // Instantiate the Payne-Hanek module
    FPU_Payne_Hanek dut (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .angle_in(angle_in),
        .angle_out(angle_out),
        .quadrant(quadrant),
        .done(done),
        .error(error),

        // Microcode interface
        .microcode_invoke(microcode_invoke),
        .microcode_addr(microcode_addr),
        .microcode_operand_a(microcode_operand_a),
        .microcode_done(microcode_done),
        .microcode_result(microcode_result),
        .microcode_quadrant(microcode_quadrant),
        .microcode_error(microcode_error)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    // Test counters
    integer test_num = 0;
    integer pass_count = 0;
    integer fail_count = 0;

    //=================================================================
    // Mock Microcode Responder
    //
    // Simulates microcode execution by responding to invoke signals
    // with a simple result after a delay
    //=================================================================

    reg [7:0] microcode_cycle_count;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            microcode_done <= 1'b0;
            microcode_result <= 80'd0;
            microcode_quadrant <= 2'd0;
            microcode_error <= 1'b0;
            microcode_cycle_count <= 8'd0;
        end else begin
            if (microcode_invoke) begin
                // Microcode invoked - start simulation
                microcode_done <= 1'b0;
                microcode_cycle_count <= 8'd0;
                microcode_error <= 1'b0;

                $display("  [MICROCODE] Invoked at address 0x%03X with operand 0x%020X",
                         microcode_addr, microcode_operand_a);
            end else if (microcode_cycle_count < 8'd50) begin
                // Simulate ~50 cycle microcode execution
                microcode_cycle_count <= microcode_cycle_count + 1;
            end else if (microcode_cycle_count == 8'd50) begin
                // Microcode complete - return mock result
                // For testing, just return a small angle in quadrant 0
                microcode_result <= 80'h3FFE_8000000000000000; // π/4
                microcode_quadrant <= 2'd0;
                microcode_done <= 1'b1;
                microcode_cycle_count <= microcode_cycle_count + 1;

                $display("  [MICROCODE] Completed after 50 cycles");
            end else if (microcode_cycle_count > 8'd50 && microcode_done) begin
                // Hold done for one cycle
                microcode_done <= 1'b0;
            end
        end
    end

    //=================================================================
    // Test Task
    //=================================================================

    task test_angle;
        input [79:0] angle;
        input [255:0] angle_desc;
        input expected_iterative;  // 1 if expect iterative path, 0 if expect microcode
        integer cycle_count;
        integer max_cycles;
        begin
            test_num = test_num + 1;
            $display("\n[TEST %0d] Testing: %s", test_num, angle_desc);
            $display("  Input angle: 0x%020X", angle);
            $display("  Expected path: %s", expected_iterative ? "Iterative" : "Microcode");

            // Reset microcode interface
            microcode_done = 1'b0;
            microcode_result = 80'd0;
            microcode_quadrant = 2'd0;
            microcode_error = 1'b0;

            // Apply stimulus
            @(posedge clk);
            enable = 1;
            angle_in = angle;

            // Wait for completion
            max_cycles = expected_iterative ? 500 : 100;
            cycle_count = 0;

            while (!done && cycle_count < max_cycles) begin
                @(posedge clk);
                cycle_count = cycle_count + 1;
            end

            if (!done) begin
                $display("  ✗ FAIL: Timed out waiting for completion");
                fail_count = fail_count + 1;
            end else if (error) begin
                $display("  ✗ FAIL: Module reported error");
                fail_count = fail_count + 1;
            end else begin
                $display("  Reduced angle: 0x%020X", angle_out);
                $display("  Quadrant: %0d", quadrant);
                $display("  Cycles: %0d", cycle_count);

                // Check if correct path was taken
                if (expected_iterative) begin
                    // Should NOT have invoked microcode
                    if (microcode_invoke || microcode_done) begin
                        $display("  ✗ FAIL: Incorrectly used microcode path");
                        fail_count = fail_count + 1;
                    end else begin
                        $display("  ✓ PASS: Correctly used iterative path");
                        pass_count = pass_count + 1;
                    end
                end else begin
                    // Should have invoked microcode
                    if (!microcode_done) begin
                        $display("  ✗ FAIL: Did not invoke microcode");
                        fail_count = fail_count + 1;
                    end else begin
                        $display("  ✓ PASS: Correctly used microcode path");
                        pass_count = pass_count + 1;
                    end
                end
            end

            // Deassert enable
            @(posedge clk);
            enable = 0;
            @(posedge clk);
            @(posedge clk);
        end
    endtask

    //=================================================================
    // Main Test Sequence
    //=================================================================

    initial begin
        $display("========================================");
        $display("Payne-Hanek Dispatch Logic Test");
        $display("========================================\n");

        // Initialize
        reset = 1;
        enable = 0;
        angle_in = 80'h0;
        microcode_done = 0;
        microcode_result = 80'd0;
        microcode_quadrant = 2'd0;
        microcode_error = 0;
        #20;
        reset = 0;
        #20;

        // Test 1: Small angle (2π) - should use iterative path
        test_angle(80'h4001_C90FDAA22168C235, "2π (small)", 1);

        // Test 2: Medium angle (10π) - should use iterative path
        test_angle(80'h4003_C90FDAA22168C235, "10π (small)", 1);

        // Test 3: Boundary (99π) - should use iterative path
        // 99π ≈ 311.02, exponent ≈ 0x4006 (just below threshold)
        test_angle(80'h4006_F000000000000000, "~99π (boundary, small)", 1);

        // Test 4: Boundary (100π) - should still use iterative (threshold is at 256)
        // 100π ≈ 314.16, exponent = 0x4007 - this IS at threshold
        test_angle(80'h4006_C90FDAA22168C235, "100π (boundary)", 1);

        // Test 5: Above threshold (256) - should use microcode
        // 256 = 2^8, exponent = 0x4007
        test_angle(80'h4007_8000000000000000, "256 (at threshold)", 0);

        // Test 6: Large angle (1000π) - should use microcode
        test_angle(80'h4009_C90FDAA22168C235, "1000π (large)", 0);

        // Test 7: Very large angle (10000π) - should use microcode
        test_angle(80'h400C_C90FDAA22168C235, "10000π (very large)", 0);

        // Test 8: Zero - special case, should return immediately
        test_angle(80'h0000_0000000000000000, "0.0 (special)", 1);

        // Summary
        $display("\n========================================");
        $display("Test Summary");
        $display("========================================");
        $display("Tests run:   %0d", test_num);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);

        if (fail_count == 0) begin
            $display("\n✓✓✓ ALL DISPATCH TESTS PASSED! ✓✓✓");
        end else begin
            $display("\n✗✗✗ SOME TESTS FAILED ✗✗✗");
        end

        $display("========================================\n");
        $finish;
    end

    // Timeout watchdog
    initial begin
        #100000;  // 100 us
        $display("\n✗✗✗ GLOBAL TIMEOUT ✗✗✗");
        $display("Testbench did not complete in time\n");
        $finish;
    end

endmodule
