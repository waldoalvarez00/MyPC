`timescale 1ns / 1ps

//=====================================================================
// Test for FPREM, FXTRACT and FSCALE Operations
//
// Tests the full implementations of:
// - FPREM: Partial remainder (8087 style, truncate toward zero)
// - FXTRACT: Extract exponent and significand
// - FSCALE: Scale by power of 2
//=====================================================================

module tb_fprem_fxtract_fscale;

    reg clk, reset;
    reg [4:0] operation;
    reg enable;
    reg [1:0] rounding_mode;
    reg [79:0] operand_a, operand_b;

    wire [79:0] result;
    wire [79:0] result_secondary;
    wire has_secondary;
    wire done;

    // FP80 test values
    localparam [79:0] FP_ZERO     = 80'h0000_0000_0000_0000_0000;
    localparam [79:0] FP_ONE      = 80'h3FFF_8000_0000_0000_0000;  // 1.0, exp=0
    localparam [79:0] FP_TWO      = 80'h4000_8000_0000_0000_0000;  // 2.0, exp=1
    localparam [79:0] FP_THREE    = 80'h4000_C000_0000_0000_0000;  // 3.0
    localparam [79:0] FP_FOUR     = 80'h4001_8000_0000_0000_0000;  // 4.0, exp=2
    localparam [79:0] FP_FIVE     = 80'h4001_A000_0000_0000_0000;  // 5.0
    localparam [79:0] FP_SEVEN    = 80'h4001_E000_0000_0000_0000;  // 7.0
    localparam [79:0] FP_TEN      = 80'h4002_A000_0000_0000_0000;  // 10.0
    localparam [79:0] FP_HALF     = 80'h3FFE_8000_0000_0000_0000;  // 0.5, exp=-1
    localparam [79:0] FP_INF_POS  = 80'h7FFF_8000_0000_0000_0000;  // +Inf
    localparam [79:0] FP_INF_NEG  = 80'hFFFF_8000_0000_0000_0000;  // -Inf
    localparam [79:0] FP_QNAN     = 80'h7FFF_C000_0000_0000_0000;  // QNaN
    localparam [79:0] FP_NEG_ONE  = 80'hBFFF_8000_0000_0000_0000;  // -1.0

    localparam OP_FXTRACT = 5'd23;
    localparam OP_FSCALE  = 5'd24;
    localparam OP_FPREM   = 5'd25;

    integer test_count, pass_count, fail_count;

    // Instantiate arithmetic unit
    FPU_ArithmeticUnit uut (
        .clk(clk),
        .reset(reset),
        .operation(operation),
        .enable(enable),
        .rounding_mode(rounding_mode),
        .precision_mode(2'b11),
        .operand_a(operand_a),
        .operand_b(operand_b),
        .int16_in(16'd0),
        .int32_in(32'd0),
        .uint64_in(64'd0),
        .uint64_sign_in(1'b0),
        .fp32_in(32'd0),
        .fp64_in(64'd0),
        .result(result),
        .result_secondary(result_secondary),
        .has_secondary(has_secondary),
        .int16_out(),
        .int32_out(),
        .uint64_out(),
        .uint64_sign_out(),
        .fp32_out(),
        .fp64_out(),
        .done(done),
        .cc_less(),
        .cc_equal(),
        .cc_greater(),
        .cc_unordered(),
        .flag_invalid(),
        .flag_denormal(),
        .flag_zero_divide(),
        .flag_overflow(),
        .flag_underflow(),
        .flag_inexact()
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
        $display("\nFPREM, FXTRACT and FSCALE Test Suite");
        $display("==================================================\n");

        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        reset = 1;
        enable = 0;
        operation = 0;
        rounding_mode = 0;
        operand_a = 0;
        operand_b = 0;

        @(posedge clk);
        reset = 0;
        @(posedge clk);

        // ===========================
        // FXTRACT Tests
        // ===========================
        $display("Testing FXTRACT (Extract Exponent and Significand)");
        $display("--------------------------------------------------");

        // Test 1: FXTRACT of 1.0
        // Expected: significand = 1.0, exponent = 0.0
        test_fxtract("FXTRACT(1.0)", FP_ONE, FP_ONE, FP_ZERO);

        // Test 2: FXTRACT of 2.0
        // Expected: significand = 1.0, exponent = 1.0
        test_fxtract("FXTRACT(2.0)", FP_TWO, FP_ONE, FP_ONE);

        // Test 3: FXTRACT of 4.0
        // Expected: significand = 1.0, exponent = 2.0
        test_fxtract("FXTRACT(4.0)", FP_FOUR, FP_ONE, FP_TWO);

        // Test 4: FXTRACT of 0.5
        // Expected: significand = 1.0, exponent = -1.0
        test_fxtract("FXTRACT(0.5)", FP_HALF, FP_ONE, FP_NEG_ONE);

        // Test 5: FXTRACT of +Inf
        // Expected: significand = +Inf, exponent = +Inf
        test_fxtract("FXTRACT(+Inf)", FP_INF_POS, FP_INF_POS, FP_INF_POS);

        // Test 6: FXTRACT of zero
        // Expected: significand = 0, exponent = -Inf
        test_fxtract("FXTRACT(0.0)", FP_ZERO, FP_ZERO, FP_INF_NEG);

        $display("");

        // ===========================
        // FSCALE Tests
        // ===========================
        $display("Testing FSCALE (Scale by Power of 2)");
        $display("--------------------------------------------------");

        // Test 7: FSCALE(1.0, 0.0) = 1.0 × 2^0 = 1.0
        test_fscale("FSCALE(1.0, 0)", FP_ONE, FP_ZERO, FP_ONE);

        // Test 8: FSCALE(1.0, 1.0) = 1.0 × 2^1 = 2.0
        test_fscale("FSCALE(1.0, 1)", FP_ONE, FP_ONE, FP_TWO);

        // Test 9: FSCALE(1.0, 2.0) = 1.0 × 2^2 = 4.0
        test_fscale("FSCALE(1.0, 2)", FP_ONE, FP_TWO, FP_FOUR);

        // Test 10: FSCALE(2.0, 1.0) = 2.0 × 2^1 = 4.0
        test_fscale("FSCALE(2.0, 1)", FP_TWO, FP_ONE, FP_FOUR);

        // Test 11: FSCALE(0.0, 1.0) = 0.0
        test_fscale("FSCALE(0, 1)", FP_ZERO, FP_ONE, FP_ZERO);

        // Test 12: FSCALE(+Inf, 1.0) = +Inf
        test_fscale("FSCALE(+Inf, 1)", FP_INF_POS, FP_ONE, FP_INF_POS);

        $display("");

        // ===========================
        // FPREM Tests
        // ===========================
        $display("Testing FPREM (Partial Remainder)");
        $display("--------------------------------------------------");

        // Test 13: FPREM(5.0, 3.0) = 5.0 - 1*3.0 = 2.0
        test_fprem("FPREM(5.0, 3.0)", FP_FIVE, FP_THREE, FP_TWO);

        // Test 14: FPREM(7.0, 3.0) = 7.0 - 2*3.0 = 1.0
        test_fprem("FPREM(7.0, 3.0)", FP_SEVEN, FP_THREE, FP_ONE);

        // Test 15: FPREM(10.0, 3.0) = 10.0 - 3*3.0 = 1.0
        test_fprem("FPREM(10.0, 3.0)", FP_TEN, FP_THREE, FP_ONE);

        // Test 16: FPREM(1.0, 3.0) = 1.0 (dividend < divisor)
        test_fprem("FPREM(1.0, 3.0)", FP_ONE, FP_THREE, FP_ONE);

        // Test 17: FPREM(0.0, 3.0) = 0.0
        test_fprem("FPREM(0.0, 3.0)", FP_ZERO, FP_THREE, FP_ZERO);

        // Test 18: FPREM(5.0, Inf) = 5.0 (divisor is infinity)
        test_fprem("FPREM(5.0, Inf)", FP_FIVE, FP_INF_POS, FP_FIVE);

        // Summary
        $display("");
        $display("==================================================");
        $display("Test Summary");
        $display("==================================================");
        $display("Total tests:  %0d", test_count);
        $display("Passed:       %0d", pass_count);
        $display("Failed:       %0d", fail_count);
        $display("");

        if (fail_count == 0) begin
            $display("*** ALL TESTS PASSED ***");
        end else begin
            $display("*** %0d TEST(S) FAILED ***", fail_count);
        end
        $display("");

        $finish;
    end

    // Test FXTRACT operation
    task test_fxtract;
        input [255:0] test_name;
        input [79:0] value;
        input [79:0] expected_sig;
        input [79:0] expected_exp;
        begin
            test_count = test_count + 1;
            $display("[Test %0d] %s", test_count, test_name);

            operand_a = value;
            operation = OP_FXTRACT;
            enable = 1;

            @(posedge clk);
            @(posedge clk);

            enable = 0;

            if (done && has_secondary) begin
                if (result == expected_sig && result_secondary == expected_exp) begin
                    $display("  PASS: sig=%h, exp=%h", result, result_secondary);
                    pass_count = pass_count + 1;
                end else begin
                    $display("  FAIL: sig=%h (expected %h), exp=%h (expected %h)",
                             result, expected_sig, result_secondary, expected_exp);
                    fail_count = fail_count + 1;
                end
            end else begin
                $display("  FAIL: Operation not completed or no secondary result (done=%b, has_sec=%b)", done, has_secondary);
                fail_count = fail_count + 1;
            end

            @(posedge clk);
        end
    endtask

    // Test FSCALE operation
    task test_fscale;
        input [255:0] test_name;
        input [79:0] value;
        input [79:0] scale;
        input [79:0] expected;
        begin
            test_count = test_count + 1;
            $display("[Test %0d] %s", test_count, test_name);

            operand_a = value;
            operand_b = scale;
            operation = OP_FSCALE;
            enable = 1;

            @(posedge clk);
            @(posedge clk);

            enable = 0;

            if (done) begin
                if (result == expected) begin
                    $display("  PASS: result=%h", result);
                    pass_count = pass_count + 1;
                end else begin
                    $display("  FAIL: result=%h (expected %h)", result, expected);
                    fail_count = fail_count + 1;
                end
            end else begin
                $display("  FAIL: Operation not completed");
                fail_count = fail_count + 1;
            end

            @(posedge clk);
        end
    endtask

    // Test FPREM operation
    task test_fprem;
        input [255:0] test_name;
        input [79:0] dividend;
        input [79:0] divisor;
        input [79:0] expected;
        begin
            test_count = test_count + 1;
            $display("[Test %0d] %s", test_count, test_name);

            operand_a = dividend;
            operand_b = divisor;
            operation = OP_FPREM;
            enable = 1;

            @(posedge clk);
            @(posedge clk);

            enable = 0;

            if (done) begin
                if (result == expected) begin
                    $display("  PASS: result=%h", result);
                    pass_count = pass_count + 1;
                end else begin
                    $display("  FAIL: result=%h (expected %h)", result, expected);
                    fail_count = fail_count + 1;
                end
            end else begin
                $display("  FAIL: Operation not completed");
                fail_count = fail_count + 1;
            end

            @(posedge clk);
        end
    endtask

endmodule
