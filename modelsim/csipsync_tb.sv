//============================================================================
// CSIPSync Testbench
// Tests CS:IP synchronization for atomic prefetcher updates
//============================================================================

`timescale 1ns/1ps

module csipsync_tb;

    // Clock and reset
    reg clk;
    reg reset;

    // Inputs
    reg cs_update;
    reg ip_update;
    reg [15:0] ip_in;
    reg [15:0] new_ip;
    reg propagate;

    // Outputs
    wire [15:0] ip_out;
    wire update_out;

    // Test counters
    integer tests_passed = 0;
    integer tests_failed = 0;
    integer test_num = 0;

    // Instantiate DUT
    CSIPSync dut (
        .clk(clk),
        .reset(reset),
        .cs_update(cs_update),
        .ip_update(ip_update),
        .ip_in(ip_in),
        .new_ip(new_ip),
        .propagate(propagate),
        .ip_out(ip_out),
        .update_out(update_out)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test tasks
    task check_result;
        input [15:0] expected_ip;
        input expected_update;
        input [255:0] test_name;
    begin
        test_num = test_num + 1;
        if (ip_out === expected_ip && update_out === expected_update) begin
            $display("PASS: Test %0d - %s", test_num, test_name);
            tests_passed = tests_passed + 1;
        end else begin
            $display("FAIL: Test %0d - %s", test_num, test_name);
            $display("  Expected: ip_out=0x%04x, update_out=%b", expected_ip, expected_update);
            $display("  Got:      ip_out=0x%04x, update_out=%b", ip_out, update_out);
            tests_failed = tests_failed + 1;
        end
    end
    endtask

    // Main test sequence
    initial begin
        $display("========================================");
        $display("CSIPSync Testbench");
        $display("========================================");

        // Initialize
        reset = 1;
        cs_update = 0;
        ip_update = 0;
        ip_in = 16'h0000;
        new_ip = 16'h0000;
        propagate = 0;

        // Apply reset
        #20;
        reset = 0;
        #10;

        // Test 1: Pass through ip_in when no updates
        ip_in = 16'h1234;
        new_ip = 16'hABCD;
        #1;
        check_result(16'h1234, 1'b0, "Pass through ip_in with no updates");

        // Test 2: Direct IP update with immediate propagate
        @(posedge clk);
        ip_update = 1;
        propagate = 1;
        #1;
        check_result(16'hABCD, 1'b1, "IP update with immediate propagate");

        // Test 3: IP update latched for later propagate
        @(posedge clk);
        ip_update = 0;
        propagate = 0;
        @(posedge clk);
        ip_update = 1;
        new_ip = 16'h5678;
        @(posedge clk);
        ip_update = 0;
        #1;
        check_result(16'h5678, 1'b0, "IP latched, waiting for propagate");

        // Test 4: Propagate the latched IP
        // Set propagate between clock edges to check before it clears
        @(negedge clk);
        propagate = 1;
        #1;
        check_result(16'h5678, 1'b1, "Propagate latched IP");

        // Test 5: After propagate, return to pass-through
        // The posedge with propagate=1 clears ip_updated
        @(posedge clk);
        #1;  // Wait for non-blocking assignments
        $display("DEBUG P5a: propagate=%b ip_updated=%b", propagate, dut.ip_updated);
        // Now ip_updated is cleared, set propagate=0
        propagate = 0;
        // Wait multiple cycles and use longer delay to ensure state settles
        @(posedge clk);
        #1;
        $display("DEBUG P5b: propagate=%b ip_updated=%b", propagate, dut.ip_updated);
        repeat(2) @(posedge clk);
        #5;
        // Debug: show state including internal signals
        $display("DEBUG Test5: ip_in=%h ip_update=%b propagate=%b ip_out=%h update_out=%b ip_updated=%b",
                 ip_in, ip_update, propagate, ip_out, update_out, dut.ip_updated);
        check_result(16'h1234, 1'b0, "Return to pass-through after propagate");

        // Test 6: CS update triggers update_out
        @(posedge clk);
        cs_update = 1;
        propagate = 1;
        #1;
        check_result(16'h1234, 1'b1, "CS update triggers update_out");

        // Test 7: Both CS and IP update
        @(posedge clk);
        cs_update = 0;
        propagate = 0;
        @(posedge clk);
        cs_update = 1;
        ip_update = 1;
        new_ip = 16'h9999;
        @(posedge clk);
        cs_update = 0;
        ip_update = 0;
        // Set propagate between clock edges to check before it clears
        @(negedge clk);
        propagate = 1;
        #1;
        check_result(16'h9999, 1'b1, "Both CS and IP update");

        // Test 8: Reset clears state
        @(posedge clk);
        propagate = 0;
        reset = 1;
        @(posedge clk);
        reset = 0;
        #1;
        check_result(16'h1234, 1'b0, "Reset clears state");

        // Test 9: Multiple IP updates before propagate (first wins - already latched)
        @(posedge clk);
        ip_update = 1;
        new_ip = 16'hAAAA;
        @(posedge clk);
        ip_update = 0;
        @(posedge clk);
        // The first update is already latched, subsequent updates should not override
        ip_update = 1;
        new_ip = 16'hBBBB;
        @(posedge clk);
        ip_update = 0;
        // Set propagate between clock edges to check before it clears
        @(negedge clk);
        propagate = 1;
        #1;
        // First latched value should be used (ip_updated prevents new latch)
        check_result(16'hAAAA, 1'b1, "First latched IP is used");

        // Test 10: Propagate without any updates
        @(posedge clk);
        propagate = 0;
        @(posedge clk);
        propagate = 1;
        #1;
        check_result(16'h1234, 1'b0, "Propagate without updates");

        // Summary
        @(posedge clk);
        #10;
        $display("");
        $display("========================================");
        $display("Test Summary");
        $display("========================================");
        $display("Total:  %0d", tests_passed + tests_failed);
        $display("Passed: %0d", tests_passed);
        $display("Failed: %0d", tests_failed);

        if (tests_failed == 0) begin
            $display("");
            $display("ALL TESTS PASSED");
        end else begin
            $display("");
            $display("SOME TESTS FAILED");
        end

        $display("========================================");
        $finish;
    end

endmodule
