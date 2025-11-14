// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns/1ps

//=====================================================================
// Testbench for Payne-Hanek Range Reduction Algorithm
//
// Tests the FPU_Payne_Hanek module with various large angles to verify
// correct reduction to [0, π/2) range with proper quadrant information.
//=====================================================================

module tb_payne_hanek();

    reg clk;
    reg reset;
    reg enable;
    reg [79:0] angle_in;
    wire [79:0] angle_out;
    wire [1:0] quadrant;
    wire done;
    wire error;

    // Instantiate the Payne-Hanek module
    FPU_Payne_Hanek dut (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .angle_in(angle_in),
        .angle_out(angle_out),
        .quadrant(quadrant),
        .done(done),
        .error(error)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    // Test counter
    integer test_num = 0;
    integer pass_count = 0;
    integer fail_count = 0;

    // Test task
    task test_angle;
        input [79:0] angle;
        input [31:0] angle_desc;
        input [1:0] expected_quad;
        integer cycle_count;
        begin
            test_num = test_num + 1;
            $display("\n[TEST %0d] Testing angle: %s", test_num, angle_desc);
            $display("  Input angle: 0x%020X", angle);

            // Apply stimulus
            @(posedge clk);
            enable = 1;
            angle_in = angle;

            // Wait for completion (max 500 cycles for very large angles like 1000π)
            cycle_count = 0;
            while (!done && cycle_count < 500) begin
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
                $display("  Quadrant: %0d (expected %0d)", quadrant, expected_quad);

                // Check quadrant
                if (quadrant == expected_quad) begin
                    $display("  ✓ PASS: Correct quadrant");
                    pass_count = pass_count + 1;
                end else begin
                    $display("  ✗ FAIL: Wrong quadrant");
                    fail_count = fail_count + 1;
                end
            end

            // Deassert enable
            @(posedge clk);
            enable = 0;
            @(posedge clk);
            @(posedge clk);
        end
    endtask

    // Main test sequence
    initial begin
        $display("========================================");
        $display("Payne-Hanek Range Reduction Test");
        $display("========================================\n");

        // Initialize
        reset = 1;
        enable = 0;
        angle_in = 80'h0;
        #20;
        reset = 0;
        #20;

        // Test 1: 2π (should reduce to ~0, quadrant 0)
        test_angle(80'h4001_C90FDAA22168C235, "2π", 2'd0);

        // Test 2: 3π (should reduce to π, which wraps to quadrant 2)
        test_angle(80'h4002_96CBE3F9990E9000, "3π", 2'd2);

        // Test 3: 4π (should reduce to ~0, quadrant 0)
        test_angle(80'h4002_C90FDAA22168C235, "4π", 2'd0);

        // Test 4: 10π (should reduce based on mod 2π)
        test_angle(80'h4003_C90FDAA22168C235, "10π", 2'd0);

        // Test 5: 100π (large angle test)
        test_angle(80'h4006_C90FDAA22168C235, "100π", 2'd0);

        // Test 6: Very large angle (1000π)
        test_angle(80'h4009_C90FDAA22168C235, "1000π", 2'd0);

        // Test 7: Zero (special case)
        test_angle(80'h0000_0000000000000000, "0.0", 2'd0);

        // Summary
        $display("\n========================================");
        $display("Test Summary");
        $display("========================================");
        $display("Tests run:   %0d", test_num);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);

        if (fail_count == 0) begin
            $display("\n✓✓✓ ALL TESTS PASSED! ✓✓✓");
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
