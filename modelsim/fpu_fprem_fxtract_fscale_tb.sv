`timescale 1ns / 1ps

//=====================================================================
// Comprehensive Test for FPREM, FXTRACT and FSCALE Operations
//
// Tests edge cases and missing coverage for:
// - FPREM: Partial remainder (8087 style, truncate toward zero)
// - FXTRACT: Extract exponent and significand
// - FSCALE: Scale by power of 2
//=====================================================================

module fpu_fprem_fxtract_fscale_tb;

    reg clk, reset;
    reg [4:0] operation;
    reg enable;
    reg [1:0] rounding_mode;
    reg [1:0] precision_mode;
    reg [79:0] operand_a, operand_b;

    wire [79:0] result;
    wire [79:0] result_secondary;
    wire has_secondary;
    wire done;
    wire flag_invalid;
    wire flag_zero_divide;

    // FP80 test values
    localparam [79:0] FP_ZERO     = 80'h0000_0000_0000_0000_0000;
    localparam [79:0] FP_NEG_ZERO = 80'h8000_0000_0000_0000_0000;
    localparam [79:0] FP_ONE      = 80'h3FFF_8000_0000_0000_0000;  // 1.0
    localparam [79:0] FP_NEG_ONE  = 80'hBFFF_8000_0000_0000_0000;  // -1.0
    localparam [79:0] FP_TWO      = 80'h4000_8000_0000_0000_0000;  // 2.0
    localparam [79:0] FP_THREE    = 80'h4000_C000_0000_0000_0000;  // 3.0
    localparam [79:0] FP_FOUR     = 80'h4001_8000_0000_0000_0000;  // 4.0
    localparam [79:0] FP_FIVE     = 80'h4001_A000_0000_0000_0000;  // 5.0
    localparam [79:0] FP_SEVEN    = 80'h4001_E000_0000_0000_0000;  // 7.0
    localparam [79:0] FP_EIGHT    = 80'h4002_8000_0000_0000_0000;  // 8.0
    localparam [79:0] FP_TEN      = 80'h4002_A000_0000_0000_0000;  // 10.0
    localparam [79:0] FP_SIXTEEN  = 80'h4003_8000_0000_0000_0000;  // 16.0
    localparam [79:0] FP_HALF     = 80'h3FFE_8000_0000_0000_0000;  // 0.5
    localparam [79:0] FP_QUARTER  = 80'h3FFD_8000_0000_0000_0000;  // 0.25
    localparam [79:0] FP_INF_POS  = 80'h7FFF_8000_0000_0000_0000;  // +Inf
    localparam [79:0] FP_INF_NEG  = 80'hFFFF_8000_0000_0000_0000;  // -Inf
    localparam [79:0] FP_QNAN     = 80'h7FFF_C000_0000_0000_0000;  // QNaN
    localparam [79:0] FP_SNAN     = 80'h7FFF_A000_0000_0000_0000;  // SNaN
    localparam [79:0] FP_PI       = 80'h4000_C90F_DAA2_2168_C235;  // Pi
    localparam [79:0] FP_E        = 80'h4000_ADF8_5458_A2BB_4A9A;  // e

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
        .precision_mode(precision_mode),
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
        .flag_invalid(flag_invalid),
        .flag_denormal(),
        .flag_zero_divide(flag_zero_divide),
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
        $display("\n========================================");
        $display("FPREM, FXTRACT and FSCALE Test Suite");
        $display("Comprehensive Edge Case Coverage");
        $display("========================================\n");

        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        reset = 1;
        enable = 0;
        operation = 0;
        rounding_mode = 2'b00;  // Round to nearest
        precision_mode = 2'b11; // 64-bit precision
        operand_a = 0;
        operand_b = 0;

        @(posedge clk);
        reset = 0;
        @(posedge clk);

        // ===========================
        // FXTRACT Tests
        // ===========================
        $display("=== FXTRACT Tests ===\n");

        // Basic values
        test_fxtract("FXTRACT(1.0)", FP_ONE, FP_ONE, FP_ZERO);
        test_fxtract("FXTRACT(2.0)", FP_TWO, FP_ONE, FP_ONE);
        test_fxtract("FXTRACT(4.0)", FP_FOUR, FP_ONE, FP_TWO);
        test_fxtract("FXTRACT(8.0)", FP_EIGHT, FP_ONE, FP_THREE);
        test_fxtract("FXTRACT(0.5)", FP_HALF, FP_ONE, FP_NEG_ONE);
        test_fxtract("FXTRACT(0.25)", FP_QUARTER, FP_ONE, 80'hC000_8000_0000_0000_0000);

        // Negative values
        test_fxtract("FXTRACT(-1.0)", FP_NEG_ONE, FP_NEG_ONE, FP_ZERO);
        test_fxtract("FXTRACT(-2.0)", 80'hC000_8000_0000_0000_0000, FP_NEG_ONE, FP_ONE);

        // Special values
        test_fxtract("FXTRACT(0.0)", FP_ZERO, FP_ZERO, FP_INF_NEG);
        test_fxtract("FXTRACT(-0.0)", FP_NEG_ZERO, FP_NEG_ZERO, FP_INF_NEG);
        test_fxtract("FXTRACT(+Inf)", FP_INF_POS, FP_INF_POS, FP_INF_POS);
        test_fxtract("FXTRACT(-Inf)", FP_INF_NEG, FP_INF_NEG, FP_INF_POS);
        test_fxtract_nan("FXTRACT(QNaN)", FP_QNAN);

        $display("");

        // ===========================
        // FSCALE Tests
        // ===========================
        $display("=== FSCALE Tests ===\n");

        // Basic scaling
        test_fscale("FSCALE(1.0, 0)", FP_ONE, FP_ZERO, FP_ONE);
        test_fscale("FSCALE(1.0, 1)", FP_ONE, FP_ONE, FP_TWO);
        test_fscale("FSCALE(1.0, 2)", FP_ONE, FP_TWO, FP_FOUR);
        test_fscale("FSCALE(1.0, 3)", FP_ONE, FP_THREE, FP_EIGHT);
        test_fscale("FSCALE(2.0, 1)", FP_TWO, FP_ONE, FP_FOUR);
        test_fscale("FSCALE(2.0, 2)", FP_TWO, FP_TWO, FP_EIGHT);

        // Negative scale (divide by power of 2)
        test_fscale("FSCALE(1.0, -1)", FP_ONE, FP_NEG_ONE, FP_HALF);
        test_fscale("FSCALE(2.0, -1)", FP_TWO, FP_NEG_ONE, FP_ONE);
        test_fscale("FSCALE(4.0, -2)", FP_FOUR, 80'hC000_8000_0000_0000_0000, FP_ONE);

        // Negative values
        test_fscale("FSCALE(-1.0, 1)", FP_NEG_ONE, FP_ONE, 80'hC000_8000_0000_0000_0000);

        // Special values
        test_fscale("FSCALE(0.0, 1)", FP_ZERO, FP_ONE, FP_ZERO);
        test_fscale("FSCALE(0.0, -1)", FP_ZERO, FP_NEG_ONE, FP_ZERO);
        test_fscale("FSCALE(+Inf, 1)", FP_INF_POS, FP_ONE, FP_INF_POS);
        test_fscale("FSCALE(-Inf, 1)", FP_INF_NEG, FP_ONE, FP_INF_NEG);
        test_fscale("FSCALE(1.0, +Inf)", FP_ONE, FP_INF_POS, FP_INF_POS);
        test_fscale("FSCALE(1.0, -Inf)", FP_ONE, FP_INF_NEG, FP_ZERO);

        $display("");

        // ===========================
        // FPREM Tests
        // ===========================
        $display("=== FPREM Tests ===\n");

        // Basic remainder
        test_fprem("FPREM(5.0, 3.0)", FP_FIVE, FP_THREE, FP_TWO);
        test_fprem("FPREM(7.0, 3.0)", FP_SEVEN, FP_THREE, FP_ONE);
        test_fprem("FPREM(10.0, 3.0)", FP_TEN, FP_THREE, FP_ONE);
        test_fprem("FPREM(8.0, 3.0)", FP_EIGHT, FP_THREE, FP_TWO);

        // Dividend < Divisor (quotient = 0)
        test_fprem("FPREM(1.0, 3.0)", FP_ONE, FP_THREE, FP_ONE);
        test_fprem("FPREM(2.0, 3.0)", FP_TWO, FP_THREE, FP_TWO);
        test_fprem("FPREM(0.5, 1.0)", FP_HALF, FP_ONE, FP_HALF);

        // Exact division (remainder = 0)
        test_fprem("FPREM(4.0, 2.0)", FP_FOUR, FP_TWO, FP_ZERO);
        test_fprem("FPREM(8.0, 4.0)", FP_EIGHT, FP_FOUR, FP_ZERO);

        // Same values
        test_fprem("FPREM(3.0, 3.0)", FP_THREE, FP_THREE, FP_ZERO);
        test_fprem("FPREM(1.0, 1.0)", FP_ONE, FP_ONE, FP_ZERO);

        // Special values
        test_fprem("FPREM(0.0, 3.0)", FP_ZERO, FP_THREE, FP_ZERO);
        test_fprem("FPREM(5.0, +Inf)", FP_FIVE, FP_INF_POS, FP_FIVE);

        // Invalid operations (should set flag_invalid)
        test_fprem_invalid("FPREM(+Inf, 3.0)", FP_INF_POS, FP_THREE);
        test_fprem_invalid("FPREM(5.0, 0.0)", FP_FIVE, FP_ZERO);
        test_fprem_nan("FPREM(QNaN, 3.0)", FP_QNAN, FP_THREE);
        test_fprem_nan("FPREM(5.0, QNaN)", FP_FIVE, FP_QNAN);

        // Large quotient (exp_diff = 2)
        test_fprem("FPREM(16.0, 3.0)", FP_SIXTEEN, FP_THREE, FP_ONE);

        // Summary
        $display("");
        $display("========================================");
        $display("Test Summary");
        $display("========================================");
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
                $display("  FAIL: done=%b, has_secondary=%b", done, has_secondary);
                fail_count = fail_count + 1;
            end

            @(posedge clk);
        end
    endtask

    // Test FXTRACT with NaN (just check it returns something)
    task test_fxtract_nan;
        input [255:0] test_name;
        input [79:0] value;
        begin
            test_count = test_count + 1;
            $display("[Test %0d] %s", test_count, test_name);

            operand_a = value;
            operation = OP_FXTRACT;
            enable = 1;

            @(posedge clk);
            @(posedge clk);

            enable = 0;

            if (done && has_secondary && flag_invalid) begin
                $display("  PASS: NaN handled, invalid flag set");
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: done=%b, has_secondary=%b, invalid=%b", done, has_secondary, flag_invalid);
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

    // Test FPREM invalid operation
    task test_fprem_invalid;
        input [255:0] test_name;
        input [79:0] dividend;
        input [79:0] divisor;
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

            if (done && flag_invalid) begin
                $display("  PASS: Invalid flag set correctly");
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: done=%b, invalid=%b", done, flag_invalid);
                fail_count = fail_count + 1;
            end

            @(posedge clk);
        end
    endtask

    // Test FPREM with NaN
    task test_fprem_nan;
        input [255:0] test_name;
        input [79:0] dividend;
        input [79:0] divisor;
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

            if (done && flag_invalid) begin
                $display("  PASS: NaN handled, invalid flag set");
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: done=%b, invalid=%b", done, flag_invalid);
                fail_count = fail_count + 1;
            end

            @(posedge clk);
        end
    endtask

endmodule
