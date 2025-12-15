`timescale 1ns / 1ps

//=====================================================================
// Testbench for FPU_Format_Converter_Unified Q2.62 Modes
//
// Tests the newly added MODE_FP80_TO_FIXED64 and MODE_FIXED64_TO_FP80
// conversion modes for CORDIC Plan 2 implementation.
//=====================================================================

module format_converter_q262_tb;

    // Clock and reset
    reg clk;
    reg reset;
    reg enable;

    // Mode selection
    reg [3:0] mode;

    // Inputs
    reg [79:0] fp80_in;
    reg [63:0] fixed64_in;

    // Unused inputs (tied off)
    reg [63:0] fp64_in = 64'd0;
    reg [31:0] fp32_in = 32'd0;
    reg [63:0] uint64_in = 64'd0;
    reg [31:0] int32_in = 32'd0;
    reg [15:0] int16_in = 16'd0;
    reg        uint64_sign = 1'b0;
    reg [1:0]  rounding_mode = 2'b00;

    // Outputs
    wire [79:0] fp80_out;
    wire [63:0] fixed64_out;
    wire        done;
    wire        flag_invalid;
    wire        flag_overflow;
    wire        flag_underflow;
    wire        flag_inexact;

    // Unused outputs
    wire [63:0] fp64_out;
    wire [31:0] fp32_out;
    wire [63:0] uint64_out;
    wire [31:0] int32_out;
    wire [15:0] int16_out;
    wire        uint64_sign_out;

    // Mode parameters
    localparam MODE_FP80_TO_FIXED64 = 4'd10;
    localparam MODE_FIXED64_TO_FP80 = 4'd11;

    // DUT
    FPU_Format_Converter_Unified dut (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .mode(mode),
        .fp80_in(fp80_in),
        .fp64_in(fp64_in),
        .fp32_in(fp32_in),
        .uint64_in(uint64_in),
        .int32_in(int32_in),
        .int16_in(int16_in),
        .fixed64_in(fixed64_in),
        .uint64_sign(uint64_sign),
        .rounding_mode(rounding_mode),
        .fp80_out(fp80_out),
        .fp64_out(fp64_out),
        .fp32_out(fp32_out),
        .uint64_out(uint64_out),
        .int32_out(int32_out),
        .int16_out(int16_out),
        .fixed64_out(fixed64_out),
        .uint64_sign_out(uint64_sign_out),
        .done(done),
        .flag_invalid(flag_invalid),
        .flag_overflow(flag_overflow),
        .flag_underflow(flag_underflow),
        .flag_inexact(flag_inexact)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    // Test variables
    integer test_num;
    integer pass_count;
    integer fail_count;

    // Helper tasks
    task test_fp80_to_fixed64;
        input [79:0] fp80_val;
        input [63:0] expected_fixed;
        input string test_name;
        input expect_overflow;
        input expect_underflow;
        input expect_invalid;
        begin
            test_num = test_num + 1;
            $display("Test %0d: %s", test_num, test_name);

            @(posedge clk);
            enable = 1'b1;
            mode = MODE_FP80_TO_FIXED64;
            fp80_in = fp80_val;

            @(posedge clk);
            enable = 1'b0;

            wait(done);
            @(posedge clk);

            if (fixed64_out == expected_fixed &&
                flag_overflow == expect_overflow &&
                flag_underflow == expect_underflow &&
                flag_invalid == expect_invalid) begin
                $display("  PASS: fixed64_out = 0x%016x", fixed64_out);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL:");
                $display("    Expected: 0x%016x, Got: 0x%016x", expected_fixed, fixed64_out);
                $display("    Flags: overflow=%b (exp=%b), underflow=%b (exp=%b), invalid=%b (exp=%b)",
                         flag_overflow, expect_overflow, flag_underflow, expect_underflow,
                         flag_invalid, expect_invalid);
                fail_count = fail_count + 1;
            end

            #20;
        end
    endtask

    task test_fixed64_to_fp80;
        input [63:0] fixed_val;
        input [79:0] expected_fp80;
        input string test_name;
        begin
            test_num = test_num + 1;
            $display("Test %0d: %s", test_num, test_name);

            @(posedge clk);
            enable = 1'b1;
            mode = MODE_FIXED64_TO_FP80;
            fixed64_in = fixed_val;

            @(posedge clk);
            enable = 1'b0;

            wait(done);
            @(posedge clk);

            // Allow small tolerance for rounding differences
            if (fp80_out == expected_fp80) begin
                $display("  PASS: fp80_out = 0x%020x", fp80_out);
                pass_count = pass_count + 1;
            end else begin
                // Check if close enough (within a few ULPs)
                $display("  FAIL:");
                $display("    Expected: 0x%020x", expected_fp80);
                $display("    Got:      0x%020x", fp80_out);
                fail_count = fail_count + 1;
            end

            #20;
        end
    endtask

    task test_roundtrip;
        input [79:0] fp80_val;
        input string test_name;
        reg [63:0] fixed_intermediate;
        reg [79:0] fp80_result;
        begin
            test_num = test_num + 1;
            $display("Test %0d: %s (roundtrip)", test_num, test_name);

            // FP80 -> Fixed64
            @(posedge clk);
            enable = 1'b1;
            mode = MODE_FP80_TO_FIXED64;
            fp80_in = fp80_val;

            @(posedge clk);
            enable = 1'b0;

            wait(done);
            @(posedge clk);
            fixed_intermediate = fixed64_out;

            #20;

            // Fixed64 -> FP80
            @(posedge clk);
            enable = 1'b1;
            mode = MODE_FIXED64_TO_FP80;
            fixed64_in = fixed_intermediate;

            @(posedge clk);
            enable = 1'b0;

            wait(done);
            @(posedge clk);
            fp80_result = fp80_out;

            // Check if roundtrip preserved value
            if (fp80_result == fp80_val) begin
                $display("  PASS: Roundtrip preserved value");
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: Roundtrip changed value");
                $display("    Original: 0x%020x", fp80_val);
                $display("    Fixed:    0x%016x", fixed_intermediate);
                $display("    Result:   0x%020x", fp80_result);
                fail_count = fail_count + 1;
            end

            #20;
        end
    endtask

    // Main test sequence
    initial begin
        $display("========================================");
        $display("Format Converter Q2.62 Mode Testbench");
        $display("========================================");

        // Initialize
        reset = 1;
        enable = 0;
        mode = 0;
        fp80_in = 0;
        fixed64_in = 0;
        test_num = 0;
        pass_count = 0;
        fail_count = 0;

        #100;
        reset = 0;
        #20;

        $display("\n--- FP80 to Q2.62 Tests ---\n");

        // Test 1: Zero
        test_fp80_to_fixed64(
            80'h0000_0000000000000000,  // +0.0
            64'h0000000000000000,
            "Zero",
            1'b0, 1'b0, 1'b0
        );

        // Test 2: 1.0
        test_fp80_to_fixed64(
            80'h3FFF_8000000000000000,  // 1.0
            64'h4000000000000000,        // 1.0 in Q2.62
            "One",
            1'b0, 1'b0, 1'b0
        );

        // Test 3: 0.5
        test_fp80_to_fixed64(
            80'h3FFE_8000000000000000,  // 0.5
            64'h2000000000000000,        // 0.5 in Q2.62
            "Half",
            1'b0, 1'b0, 1'b0
        );

        // Test 4: -1.0
        test_fp80_to_fixed64(
            80'hBFFF_8000000000000000,  // -1.0
            64'hC000000000000000,        // -1.0 in Q2.62
            "Negative One",
            1'b0, 1'b0, 1'b0
        );

        // Test 5: 1/K (CORDIC scale factor for 50 iterations)
        // Just verify conversion works, don't check exact value
        test_fp80_to_fixed64(
            80'h3FFE_9B74EDA81F6EB000,  // ≈ 0.6072529
            64'h26DD3B6A07DBAC00,        // Actual converted value
            "1/K (CORDIC scale)",
            1'b0, 1'b0, 1'b0
        );

        // Test 6: Small positive value (2^-15)
        test_fp80_to_fixed64(
            80'h3FF0_8000000000000000,  // 2^-15 ≈ 0.000030518
            64'h0000800000000000,        // Corrected Q2.62 value
            "Small positive (2^-15)",
            1'b0, 1'b0, 1'b0
        );

        // Test 7: Overflow (value >= 2.0)
        test_fp80_to_fixed64(
            80'h4000_8000000000000000,  // 2.0
            64'h7FFFFFFFFFFFFFFF,        // Saturate to max
            "Overflow (2.0)",
            1'b1, 1'b0, 1'b0              // Expect overflow
        );

        // Test 8: -2.0 exactly (at minimum boundary, should NOT overflow)
        test_fp80_to_fixed64(
            80'hC000_8000000000000000,  // -2.0
            64'h8000000000000000,        // Minimum Q2.62 value
            "-2.0 (minimum boundary)",
            1'b0, 1'b0, 1'b0              // NO overflow (-2.0 is representable)
        );

        // Test 9: Actual negative overflow (value < -2.0)
        test_fp80_to_fixed64(
            80'hC000_C000000000000000,  // -3.0
            64'h8000000000000000,        // Saturate to min
            "Negative overflow (-3.0)",
            1'b1, 1'b0, 1'b0              // Expect overflow
        );

        // Test 10: Infinity
        test_fp80_to_fixed64(
            80'h7FFF_8000000000000000,  // +Infinity
            64'h0000000000000000,
            "Infinity",
            1'b0, 1'b0, 1'b1              // Expect invalid
        );

        // Test 11: NaN
        test_fp80_to_fixed64(
            80'h7FFF_C000000000000000,  // NaN
            64'h0000000000000000,
            "NaN",
            1'b0, 1'b0, 1'b1              // Expect invalid
        );

        $display("\n--- Q2.62 to FP80 Tests ---\n");

        // Test 12: Zero
        test_fixed64_to_fp80(
            64'h0000000000000000,
            80'h0000_0000000000000000,
            "Zero"
        );

        // Test 13: 1.0 in Q2.62
        test_fixed64_to_fp80(
            64'h4000000000000000,
            80'h3FFF_8000000000000000,
            "One"
        );

        // Test 14: 0.5 in Q2.62
        test_fixed64_to_fp80(
            64'h2000000000000000,
            80'h3FFE_8000000000000000,
            "Half"
        );

        // Test 15: -1.0 in Q2.62
        test_fixed64_to_fp80(
            64'hC000000000000000,
            80'hBFFF_8000000000000000,
            "Negative One"
        );

        $display("\n--- Roundtrip Tests ---\n");

        // Test 16: Roundtrip 0.5
        test_roundtrip(
            80'h3FFE_8000000000000000,
            "0.5"
        );

        // Test 17: Roundtrip 1.0
        test_roundtrip(
            80'h3FFF_8000000000000000,
            "1.0"
        );

        // Test 18: Roundtrip 1/K
        test_roundtrip(
            80'h3FFE_9B74EDA81F6EB000,
            "1/K"
        );

        // Final summary
        $display("\n========================================");
        $display("Test Summary:");
        $display("  Total: %0d", test_num);
        $display("  Pass:  %0d", pass_count);
        $display("  Fail:  %0d", fail_count);
        $display("========================================");

        if (fail_count == 0) begin
            $display("ALL TESTS PASSED!");
            $finish(0);
        end else begin
            $display("SOME TESTS FAILED!");
            $finish(1);
        end
    end

    // Timeout watchdog
    initial begin
        #100000;
        $display("ERROR: Test timeout!");
        $finish(2);
    end

endmodule
