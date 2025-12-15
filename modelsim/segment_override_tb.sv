//============================================================================
// SegmentOverride Testbench
// Tests segment override prefix handling for x86 instructions
//============================================================================

`timescale 1ns/1ps

module segment_override_tb;

    // Segment register constants
    localparam [1:0] ES = 2'b00;
    localparam [1:0] CS = 2'b01;
    localparam [1:0] SS = 2'b10;
    localparam [1:0] DS = 2'b11;

    // Clock and reset
    reg clk;
    reg reset;

    // Inputs
    reg next_instruction;
    reg flush;
    reg update;
    reg force_segment;
    reg bp_is_base;
    reg segment_override;
    reg [1:0] override_in;
    reg [1:0] microcode_sr_rd_sel;

    // Output
    wire [1:0] sr_rd_sel;

    // Test counters
    integer tests_passed = 0;
    integer tests_failed = 0;
    integer test_num = 0;

    // Instantiate DUT
    SegmentOverride dut (
        .clk(clk),
        .reset(reset),
        .next_instruction(next_instruction),
        .flush(flush),
        .update(update),
        .force_segment(force_segment),
        .bp_is_base(bp_is_base),
        .segment_override(segment_override),
        .override_in(override_in),
        .microcode_sr_rd_sel(microcode_sr_rd_sel),
        .sr_rd_sel(sr_rd_sel)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test tasks
    task check_result;
        input [1:0] expected_sel;
        input [255:0] test_name;
    begin
        test_num = test_num + 1;
        if (sr_rd_sel === expected_sel) begin
            $display("PASS: Test %0d - %s", test_num, test_name);
            tests_passed = tests_passed + 1;
        end else begin
            $display("FAIL: Test %0d - %s", test_num, test_name);
            $display("  Expected: sr_rd_sel=%b (%s)", expected_sel,
                expected_sel == ES ? "ES" : expected_sel == CS ? "CS" :
                expected_sel == SS ? "SS" : "DS");
            $display("  Got:      sr_rd_sel=%b (%s)", sr_rd_sel,
                sr_rd_sel == ES ? "ES" : sr_rd_sel == CS ? "CS" :
                sr_rd_sel == SS ? "SS" : "DS");
            tests_failed = tests_failed + 1;
        end
    end
    endtask

    // Main test sequence
    initial begin
        $display("========================================");
        $display("SegmentOverride Testbench");
        $display("========================================");

        // Initialize
        reset = 1;
        next_instruction = 0;
        flush = 0;
        update = 0;
        force_segment = 0;
        bp_is_base = 0;
        segment_override = 0;
        override_in = DS;
        microcode_sr_rd_sel = DS;

        // Apply reset
        #20;
        reset = 0;
        #10;

        // Test 1: Default - pass through microcode segment
        microcode_sr_rd_sel = DS;
        #1;
        check_result(DS, "Default microcode segment (DS)");

        // Test 2: Different microcode segment
        microcode_sr_rd_sel = CS;
        #1;
        check_result(CS, "Different microcode segment (CS)");

        // Test 3: BP is base - should use SS
        bp_is_base = 1;
        #1;
        check_result(SS, "BP is base - use SS");

        // Test 4: Force segment overrides BP
        force_segment = 1;
        microcode_sr_rd_sel = ES;
        #1;
        check_result(ES, "Force segment overrides BP");

        // Test 5: Segment override prefix - immediate effect
        force_segment = 0;
        bp_is_base = 0;
        update = 1;
        segment_override = 1;
        override_in = CS;
        #1;
        check_result(CS, "Segment override prefix - immediate CS");

        // Test 6: Latch segment override
        @(posedge clk);
        update = 0;
        segment_override = 0;
        microcode_sr_rd_sel = DS;
        #1;
        check_result(CS, "Latched segment override (CS)");

        // Test 7: Override persists across cycles
        @(posedge clk);
        @(posedge clk);
        #1;
        check_result(CS, "Override persists across cycles");

        // Test 8: Next instruction clears override
        @(posedge clk);
        next_instruction = 1;
        @(posedge clk);
        next_instruction = 0;
        #1;
        check_result(DS, "Next instruction clears override");

        // Test 9: Override to ES
        @(posedge clk);
        update = 1;
        segment_override = 1;
        override_in = ES;
        @(posedge clk);
        update = 0;
        segment_override = 0;
        #1;
        check_result(ES, "Override to ES");

        // Test 10: Flush clears override
        @(posedge clk);
        flush = 1;
        @(posedge clk);
        flush = 0;
        #1;
        check_result(DS, "Flush clears override");

        // Test 11: Override to SS
        @(posedge clk);
        update = 1;
        segment_override = 1;
        override_in = SS;
        @(posedge clk);
        update = 0;
        segment_override = 0;
        #1;
        check_result(SS, "Override to SS");

        // Test 12: Force segment takes priority over latched override
        force_segment = 1;
        microcode_sr_rd_sel = ES;
        #1;
        check_result(ES, "Force segment priority over latched");

        // Test 13: Reset clears everything
        @(posedge clk);
        force_segment = 0;
        reset = 1;
        @(posedge clk);
        reset = 0;
        microcode_sr_rd_sel = DS;
        #1;
        check_result(DS, "Reset clears override");

        // Test 14: BP base with override - override wins
        @(posedge clk);
        bp_is_base = 1;
        update = 1;
        segment_override = 1;
        override_in = ES;
        @(posedge clk);
        update = 0;
        segment_override = 0;
        #1;
        check_result(ES, "Override takes priority over BP base");

        // Test 15: After clearing override, BP base applies again
        @(posedge clk);
        next_instruction = 1;
        @(posedge clk);
        next_instruction = 0;
        #1;
        check_result(SS, "After clear, BP base applies");

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
