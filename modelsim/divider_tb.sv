// Testbench for CPU Divider module
// Tests DIV/IDIV instructions (8-bit and 16-bit, signed and unsigned)

`timescale 1ns/1ps

module divider_tb;

    // Clock and reset
    logic        clk;
    logic        reset;

    // Control signals
    logic        start;
    logic        is_8_bit;
    logic        is_signed;

    // Data signals
    logic [31:0] dividend;
    logic [15:0] divisor;
    logic [15:0] quotient;
    logic [15:0] remainder;

    // Status signals
    logic        busy;
    logic        complete;
    logic        error;

    // Test tracking
    int test_num = 0;
    int errors = 0;
    int passed_tests = 0;

    // DUT instantiation
    Divider dut(
        .clk(clk),
        .reset(reset),
        .start(start),
        .is_8_bit(is_8_bit),
        .is_signed(is_signed),
        .busy(busy),
        .complete(complete),
        .error(error),
        .dividend(dividend),
        .divisor(divisor),
        .quotient(quotient),
        .remainder(remainder)
    );

    // Clock generation: 50 MHz
    initial begin
        clk = 0;
        forever #10 clk = ~clk;  // 20ns period = 50 MHz
    end

    // Test stimulus
    initial begin
        $display("========================================");
        $display("Divider Unit Test");
        $display("========================================");

        // Initialize signals
        reset = 1;
        start = 0;
        is_8_bit = 0;
        is_signed = 0;
        dividend = 32'd0;
        divisor = 16'd0;

        // Apply reset
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        // Test 1: 8-bit unsigned division - simple case
        test_1_8bit_unsigned_simple();

        // Test 2: 8-bit unsigned division - with remainder
        test_2_8bit_unsigned_remainder();

        // Test 3: 16-bit unsigned division - simple case
        test_3_16bit_unsigned_simple();

        // Test 4: 16-bit unsigned division - with remainder
        test_4_16bit_unsigned_remainder();

        // Test 5: 8-bit signed division - positive/positive
        test_5_8bit_signed_pos_pos();

        // Test 6: 8-bit signed division - positive/negative
        test_6_8bit_signed_pos_neg();

        // Test 7: 8-bit signed division - negative/positive
        test_7_8bit_signed_neg_pos();

        // Test 8: 8-bit signed division - negative/negative
        test_8_8bit_signed_neg_neg();

        // Test 9: 16-bit signed division - positive/positive
        test_9_16bit_signed_pos_pos();

        // Test 10: 16-bit signed division - mixed signs
        test_10_16bit_signed_mixed();

        // Test 11: Division by zero - error case
        test_11_divide_by_zero();

        // Test 12: Overflow condition
        test_12_overflow();

        // Test 13: Edge case - divide by 1
        test_13_divide_by_one();

        // Test 14: Edge case - dividend smaller than divisor
        test_14_dividend_smaller();

        // Final results
        repeat(10) @(posedge clk);
        $display("\n========================================");
        $display("Test Summary:");
        $display("  Total Tests: %0d", test_num);
        $display("  Passed:      %0d", passed_tests);
        $display("  Failed:      %0d", errors);
        $display("========================================");

        if (errors == 0)
            $display("✓ ALL TESTS PASSED");
        else
            $display("✗ SOME TESTS FAILED");

        $finish;
    end

    // Task: Perform division and wait for completion
    task do_divide(
        input [31:0] div_dividend,
        input [15:0] div_divisor,
        input        div_is_8bit,
        input        div_is_signed
    );
        integer i;
        begin
            dividend = div_dividend;
            divisor = div_divisor;
            is_8_bit = div_is_8bit;
            is_signed = div_is_signed;
            start = 1;
            @(posedge clk);
            start = 0;

            // Wait for completion or error (max 50 cycles)
            for (i = 0; i < 50; i = i + 1) begin
                @(posedge clk);
                if (complete || error)
                    i = 50;  // Exit loop condition
            end

            // Extra cycle to ensure outputs stable
            @(posedge clk);
        end
    endtask

    // Test 1: 8-bit unsigned: 100 / 5 = 20, rem 0
    task test_1_8bit_unsigned_simple();
        begin
            test_num++;
            $display("\nTest %0d: 8-bit unsigned division (100 / 5)", test_num);

            do_divide(32'd100, 16'd5, 1'b1, 1'b0);

            if (!error && quotient[7:0] == 8'd20 && remainder[7:0] == 8'd0) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", quotient[7:0], remainder[7:0]);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=20, R=0; Got Q=%0d, R=%0d, error=%b",
                         quotient[7:0], remainder[7:0], error);
                errors++;
            end
        end
    endtask

    // Test 2: 8-bit unsigned: 101 / 5 = 20, rem 1
    task test_2_8bit_unsigned_remainder();
        begin
            test_num++;
            $display("\nTest %0d: 8-bit unsigned division with remainder (101 / 5)", test_num);

            do_divide(32'd101, 16'd5, 1'b1, 1'b0);

            if (!error && quotient[7:0] == 8'd20 && remainder[7:0] == 8'd1) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", quotient[7:0], remainder[7:0]);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=20, R=1; Got Q=%0d, R=%0d, error=%b",
                         quotient[7:0], remainder[7:0], error);
                errors++;
            end
        end
    endtask

    // Test 3: 16-bit unsigned: 10000 / 100 = 100, rem 0
    task test_3_16bit_unsigned_simple();
        begin
            test_num++;
            $display("\nTest %0d: 16-bit unsigned division (10000 / 100)", test_num);

            do_divide(32'd10000, 16'd100, 1'b0, 1'b0);

            if (!error && quotient == 16'd100 && remainder == 16'd0) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", quotient, remainder);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=100, R=0; Got Q=%0d, R=%0d, error=%b",
                         quotient, remainder, error);
                errors++;
            end
        end
    endtask

    // Test 4: 16-bit unsigned: 12345 / 100 = 123, rem 45
    task test_4_16bit_unsigned_remainder();
        begin
            test_num++;
            $display("\nTest %0d: 16-bit unsigned division with remainder (12345 / 100)", test_num);

            do_divide(32'd12345, 16'd100, 1'b0, 1'b0);

            if (!error && quotient == 16'd123 && remainder == 16'd45) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", quotient, remainder);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=123, R=45; Got Q=%0d, R=%0d, error=%b",
                         quotient, remainder, error);
                errors++;
            end
        end
    endtask

    // Test 5: 8-bit signed: 100 / 5 = 20, rem 0 (both positive)
    task test_5_8bit_signed_pos_pos();
        begin
            test_num++;
            $display("\nTest %0d: 8-bit signed division +100 / +5", test_num);

            do_divide(32'd100, 16'd5, 1'b1, 1'b1);

            if (!error && $signed(quotient[7:0]) == 8'sd20 && $signed(remainder[7:0]) == 8'sd0) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", $signed(quotient[7:0]), $signed(remainder[7:0]));
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=20, R=0; Got Q=%0d, R=%0d, error=%b",
                         $signed(quotient[7:0]), $signed(remainder[7:0]), error);
                errors++;
            end
        end
    endtask

    // Test 6: 8-bit signed: 100 / -5 = -20 (positive / negative)
    task test_6_8bit_signed_pos_neg();
        begin
            test_num++;
            $display("\nTest %0d: 8-bit signed division +100 / -5", test_num);

            do_divide(32'd100, 16'hFFFB, 1'b1, 1'b1);  // -5 in 16-bit two's complement

            if (!error && $signed(quotient[7:0]) == -8'sd20) begin
                $display("  ✓ Result correct: Q=%0d", $signed(quotient[7:0]));
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=-20; Got Q=%0d, error=%b",
                         $signed(quotient[7:0]), error);
                errors++;
            end
        end
    endtask

    // Test 7: 8-bit signed: -100 / 5 = -20 (negative / positive)
    task test_7_8bit_signed_neg_pos();
        begin
            test_num++;
            $display("\nTest %0d: 8-bit signed division -100 / +5", test_num);

            // -100 in 16-bit space for 8-bit division: 0xFF9C (sign-extended)
            do_divide(32'hFFFF_FF9C, 16'd5, 1'b1, 1'b1);

            if (!error && $signed(quotient[7:0]) == -8'sd20) begin
                $display("  ✓ Result correct: Q=%0d", $signed(quotient[7:0]));
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=-20; Got Q=%0d, error=%b",
                         $signed(quotient[7:0]), error);
                errors++;
            end
        end
    endtask

    // Test 8: 8-bit signed: -100 / -5 = 20 (negative / negative)
    task test_8_8bit_signed_neg_neg();
        begin
            test_num++;
            $display("\nTest %0d: 8-bit signed division -100 / -5", test_num);

            do_divide(32'hFFFF_FF9C, 16'hFFFB, 1'b1, 1'b1);

            if (!error && $signed(quotient[7:0]) == 8'sd20) begin
                $display("  ✓ Result correct: Q=%0d", $signed(quotient[7:0]));
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=20; Got Q=%0d, error=%b",
                         $signed(quotient[7:0]), error);
                errors++;
            end
        end
    endtask

    // Test 9: 16-bit signed: 1000 / 10 = 100 (both positive)
    task test_9_16bit_signed_pos_pos();
        begin
            test_num++;
            $display("\nTest %0d: 16-bit signed division +1000 / +10", test_num);

            do_divide(32'd1000, 16'd10, 1'b0, 1'b1);

            if (!error && $signed(quotient) == 16'sd100 && $signed(remainder) == 16'sd0) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", $signed(quotient), $signed(remainder));
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=100, R=0; Got Q=%0d, R=%0d, error=%b",
                         $signed(quotient), $signed(remainder), error);
                errors++;
            end
        end
    endtask

    // Test 10: 16-bit signed: -1000 / 10 = -100 (mixed signs)
    task test_10_16bit_signed_mixed();
        begin
            test_num++;
            $display("\nTest %0d: 16-bit signed division -1000 / +10", test_num);

            do_divide(32'hFFFF_FC18, 16'd10, 1'b0, 1'b1);  // -1000 in 32-bit

            if (!error && $signed(quotient) == -16'sd100) begin
                $display("  ✓ Result correct: Q=%0d", $signed(quotient));
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=-100; Got Q=%0d, error=%b",
                         $signed(quotient), error);
                errors++;
            end
        end
    endtask

    // Test 11: Division by zero
    task test_11_divide_by_zero();
        begin
            test_num++;
            $display("\nTest %0d: Division by zero (100 / 0)", test_num);

            do_divide(32'd100, 16'd0, 1'b0, 1'b0);

            if (error) begin
                $display("  ✓ Error correctly raised for division by zero");
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected error flag, got error=%b", error);
                errors++;
            end
        end
    endtask

    // Test 12: Overflow condition (dividend too large for quotient)
    task test_12_overflow();
        begin
            test_num++;
            $display("\nTest %0d: Overflow condition (65535 / 1)", test_num);

            // For 8-bit division: dividend >= divisor << 8 causes overflow
            do_divide(32'h0000_FF00, 16'd1, 1'b1, 1'b0);

            if (error) begin
                $display("  ✓ Overflow correctly detected");
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected overflow error, got error=%b", error);
                errors++;
            end
        end
    endtask

    // Test 13: Divide by 1 (should return dividend)
    task test_13_divide_by_one();
        begin
            test_num++;
            $display("\nTest %0d: Divide by 1 (123 / 1)", test_num);

            do_divide(32'd123, 16'd1, 1'b0, 1'b0);

            if (!error && quotient == 16'd123 && remainder == 16'd0) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", quotient, remainder);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=123, R=0; Got Q=%0d, R=%0d, error=%b",
                         quotient, remainder, error);
                errors++;
            end
        end
    endtask

    // Test 14: Dividend smaller than divisor (quotient = 0, remainder = dividend)
    task test_14_dividend_smaller();
        begin
            test_num++;
            $display("\nTest %0d: Dividend < divisor (5 / 10)", test_num);

            do_divide(32'd5, 16'd10, 1'b0, 1'b0);

            if (!error && quotient == 16'd0 && remainder == 16'd5) begin
                $display("  ✓ Result correct: Q=%0d, R=%0d", quotient, remainder);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected Q=0, R=5; Got Q=%0d, R=%0d, error=%b",
                         quotient, remainder, error);
                errors++;
            end
        end
    endtask

    // Timeout watchdog
    initial begin
        #1000000;  // 1ms timeout
        $display("\n✗ TIMEOUT: Test did not complete");
        $finish;
    end

endmodule
