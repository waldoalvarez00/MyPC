`timescale 1ns / 1ps

//=====================================================================
// CORDIC Wrapper Integration Testbench with Real Arithmetic Units
//
// Tests Plan 2 (Heavy Unit Reuse) implementation with actual
// FPU_IEEE754_AddSub and FPU_IEEE754_MulDiv_Unified units.
//
// Tests:
// - ATAN mode with 16 iterations + polynomial correction
// - TAN mode with 16 iterations + polynomial correction
// - Accuracy verification against known values
// - Shared unit arbitration
//=====================================================================

module cordic_correction_integration_tb;

    // Clock and reset
    reg clk;
    reg reset;

    // CORDIC wrapper control
    reg        cordic_enable;
    reg [1:0]  cordic_mode;
    reg [79:0] cordic_angle_in;
    reg [79:0] cordic_x_in;
    reg [79:0] cordic_y_in;

    wire [79:0] cordic_sin_out;
    wire [79:0] cordic_cos_out;
    wire [79:0] cordic_atan_out;
    wire [79:0] cordic_magnitude_out;
    wire [79:0] cordic_tan_out;
    wire        cordic_done;
    wire        cordic_error;

    // Shared arithmetic unit signals
    wire        cordic_addsub_req;
    wire [79:0] cordic_addsub_a;
    wire [79:0] cordic_addsub_b;
    wire        cordic_addsub_sub;
    reg  [79:0] cordic_addsub_result;
    reg         cordic_addsub_done;
    reg         cordic_addsub_invalid;

    wire        cordic_muldiv_req;
    wire        cordic_muldiv_op;
    wire [79:0] cordic_muldiv_a;
    wire [79:0] cordic_muldiv_b;
    reg  [79:0] cordic_muldiv_result;
    reg         cordic_muldiv_done;
    reg         cordic_muldiv_invalid;

    // AddSub unit
    reg        addsub_enable;
    reg [79:0] addsub_operand_a;
    reg [79:0] addsub_operand_b;
    reg        addsub_subtract;
    wire [79:0] addsub_result;
    wire        addsub_done;
    wire        addsub_flag_invalid;
    wire        addsub_flag_overflow;
    wire        addsub_flag_underflow;
    wire        addsub_flag_inexact;

    // MulDiv unit
    reg        muldiv_enable;
    reg        muldiv_operation;  // 0=mul, 1=div
    reg [79:0] muldiv_operand_a;
    reg [79:0] muldiv_operand_b;
    wire [79:0] muldiv_result;
    wire        muldiv_done;
    wire        muldiv_flag_invalid;
    wire        muldiv_flag_div_by_zero;
    wire        muldiv_flag_overflow;
    wire        muldiv_flag_underflow;
    wire        muldiv_flag_inexact;

    // Test parameters
    localparam MODE_ROTATION  = 2'b00;  // SIN/COS
    localparam MODE_VECTORING = 2'b01;  // ATAN
    localparam MODE_TAN       = 2'b10;  // TAN

    // FP80 constants for testing
    localparam FP80_ZERO     = 80'h0000_0000000000000000;
    localparam FP80_ONE      = 80'h3FFF_8000000000000000;
    localparam FP80_HALF     = 80'h3FFE_8000000000000000;
    localparam FP80_PI_DIV_4 = 80'h3FFE_C90FDAA22168C235;  // π/4 ≈ 0.785398163
    localparam FP80_PI_DIV_6 = 80'h3FFE_860A91C16B9B2C23;  // π/6 ≈ 0.523598776

    //=================================================================
    // DUT: CORDIC Wrapper
    //=================================================================

    FPU_CORDIC_Wrapper cordic_dut (
        .clk(clk),
        .reset(reset),
        .enable(cordic_enable),
        .mode(cordic_mode),
        .angle_in(cordic_angle_in),
        .x_in(cordic_x_in),
        .y_in(cordic_y_in),
        .sin_out(cordic_sin_out),
        .cos_out(cordic_cos_out),
        .atan_out(cordic_atan_out),
        .magnitude_out(cordic_magnitude_out),
        .tan_out(cordic_tan_out),
        .done(cordic_done),
        .error(cordic_error),
        // Shared unit interface
        .ext_addsub_req(cordic_addsub_req),
        .ext_addsub_a(cordic_addsub_a),
        .ext_addsub_b(cordic_addsub_b),
        .ext_addsub_sub(cordic_addsub_sub),
        .ext_addsub_result(cordic_addsub_result),
        .ext_addsub_done(cordic_addsub_done),
        .ext_addsub_invalid(cordic_addsub_invalid),
        .ext_muldiv_req(cordic_muldiv_req),
        .ext_muldiv_op(cordic_muldiv_op),
        .ext_muldiv_a(cordic_muldiv_a),
        .ext_muldiv_b(cordic_muldiv_b),
        .ext_muldiv_result(cordic_muldiv_result),
        .ext_muldiv_done(cordic_muldiv_done),
        .ext_muldiv_invalid(cordic_muldiv_invalid)
    );

    //=================================================================
    // Real FPU Arithmetic Units
    //=================================================================

    FPU_IEEE754_AddSub addsub_unit (
        .clk(clk),
        .reset(reset),
        .enable(addsub_enable),
        .operand_a(addsub_operand_a),
        .operand_b(addsub_operand_b),
        .subtract(addsub_subtract),
        .rounding_mode(2'b00),  // Round to nearest
        .result(addsub_result),
        .done(addsub_done),
        .cmp_equal(),
        .cmp_less(),
        .cmp_greater(),
        .flag_invalid(addsub_flag_invalid),
        .flag_overflow(addsub_flag_overflow),
        .flag_underflow(addsub_flag_underflow),
        .flag_inexact(addsub_flag_inexact)
    );

    FPU_IEEE754_MulDiv_Unified muldiv_unit (
        .clk(clk),
        .reset(reset),
        .enable(muldiv_enable),
        .operation(muldiv_operation),
        .operand_a(muldiv_operand_a),
        .operand_b(muldiv_operand_b),
        .rounding_mode(2'b00),  // Round to nearest
        .result(muldiv_result),
        .done(muldiv_done),
        .flag_invalid(muldiv_flag_invalid),
        .flag_div_by_zero(muldiv_flag_div_by_zero),
        .flag_overflow(muldiv_flag_overflow),
        .flag_underflow(muldiv_flag_underflow),
        .flag_inexact(muldiv_flag_inexact)
    );

    //=================================================================
    // Simple Arbiter: Routes CORDIC requests to arithmetic units
    //=================================================================

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            addsub_enable <= 1'b0;
            addsub_operand_a <= 80'd0;
            addsub_operand_b <= 80'd0;
            addsub_subtract <= 1'b0;
            cordic_addsub_result <= 80'd0;
            cordic_addsub_done <= 1'b0;
            cordic_addsub_invalid <= 1'b0;

            muldiv_enable <= 1'b0;
            muldiv_operation <= 1'b0;
            muldiv_operand_a <= 80'd0;
            muldiv_operand_b <= 80'd0;
            cordic_muldiv_result <= 80'd0;
            cordic_muldiv_done <= 1'b0;
            cordic_muldiv_invalid <= 1'b0;
        end else begin
            // AddSub request handling
            if (cordic_addsub_req && !addsub_enable) begin
                addsub_enable <= 1'b1;
                addsub_operand_a <= cordic_addsub_a;
                addsub_operand_b <= cordic_addsub_b;
                addsub_subtract <= cordic_addsub_sub;
                cordic_addsub_done <= 1'b0;
            end else if (addsub_enable && !cordic_addsub_req) begin
                addsub_enable <= 1'b0;
            end

            // AddSub result
            if (addsub_done) begin
                cordic_addsub_result <= addsub_result;
                cordic_addsub_done <= 1'b1;
                cordic_addsub_invalid <= addsub_flag_invalid;
            end else begin
                cordic_addsub_done <= 1'b0;
            end

            // MulDiv request handling
            if (cordic_muldiv_req && !muldiv_enable) begin
                muldiv_enable <= 1'b1;
                muldiv_operation <= cordic_muldiv_op;
                muldiv_operand_a <= cordic_muldiv_a;
                muldiv_operand_b <= cordic_muldiv_b;
                cordic_muldiv_done <= 1'b0;
            end else if (muldiv_enable && !cordic_muldiv_req) begin
                muldiv_enable <= 1'b0;
            end

            // MulDiv result
            if (muldiv_done) begin
                cordic_muldiv_result <= muldiv_result;
                cordic_muldiv_done <= 1'b1;
                cordic_muldiv_invalid <= muldiv_flag_invalid || muldiv_flag_div_by_zero;
            end else begin
                cordic_muldiv_done <= 1'b0;
            end
        end
    end

    //=================================================================
    // Clock generation
    //=================================================================

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    //=================================================================
    // Test variables
    //=================================================================

    integer test_num;
    integer pass_count;
    integer fail_count;
    reg [79:0] expected_result;
    real expected_float;
    real actual_float;
    real error_ulps;

    //=================================================================
    // Helper tasks
    //=================================================================

    // Convert FP80 to real for comparison (simplified)
    // Note: This is approximate - Verilog real has ~53-bit precision vs FP80's 64-bit
    function real fp80_to_real;
        input [79:0] fp80_val;
        reg sign;
        integer exp_signed;
        real mant_real;
        real result;
        integer i;
        begin
            sign = fp80_val[79];

            // Handle special cases
            if (fp80_val[78:64] == 15'd0) begin
                // Zero or denormal
                fp80_to_real = 0.0;
            end else if (fp80_val[78:64] == 15'h7FFF) begin
                // Infinity or NaN
                fp80_to_real = sign ? -1e308 : 1e308;
            end else begin
                // Normalized value
                // FP80: value = mant * 2^(exp - 16383 - 63)

                // Convert mantissa to real (bits 63:0)
                // This is approximate but good enough for comparison
                mant_real = 0.0;
                for (i = 63; i >= 0; i = i - 1) begin
                    if (fp80_val[i]) begin
                        // Add 2^(i-63) to mantissa
                        if (i == 63) mant_real = mant_real + 1.0;
                        else if (i == 62) mant_real = mant_real + 0.5;
                        else if (i == 61) mant_real = mant_real + 0.25;
                        else if (i == 60) mant_real = mant_real + 0.125;
                        else if (i >= 50) mant_real = mant_real + (1.0 / (1 << (63-i)));
                        // For lower bits, contribution is too small for real precision
                    end
                end

                // Calculate exponent scaling: 2^(exp - 16383 - 63)
                exp_signed = fp80_val[78:64] - 16383 - 63;

                // Apply exponent by repeated multiplication/division
                result = mant_real;
                if (exp_signed > 0) begin
                    for (i = 0; i < exp_signed && i < 1000; i = i + 1) begin
                        result = result * 2.0;
                    end
                end else if (exp_signed < 0) begin
                    for (i = 0; i > exp_signed && i > -1000; i = i - 1) begin
                        result = result / 2.0;
                    end
                end

                fp80_to_real = sign ? -result : result;
            end
        end
    endfunction

    task test_atan;
        input [79:0] x_val;
        input [79:0] y_val;
        input [79:0] expected;
        input string test_name;
        real x_real, y_real, expected_val, actual_val, error;
        begin
            test_num = test_num + 1;
            $display("Test %0d: ATAN %s", test_num, test_name);

            x_real = fp80_to_real(x_val);
            y_real = fp80_to_real(y_val);
            expected_val = fp80_to_real(expected);

            @(posedge clk);
            cordic_enable = 1'b1;
            cordic_mode = MODE_VECTORING;
            cordic_x_in = x_val;
            cordic_y_in = y_val;

            @(posedge clk);
            cordic_enable = 1'b0;

            // Wait for completion (with timeout)
            fork
                wait(cordic_done);
                begin
                    #500000;  // 500 us timeout
                    $display("  TIMEOUT!");
                end
            join_any
            disable fork;

            if (!cordic_done) begin
                $display("  FAIL: Operation timed out");
                fail_count = fail_count + 1;
            end else if (cordic_error) begin
                $display("  FAIL: Error flag set");
                fail_count = fail_count + 1;
            end else begin
                actual_val = fp80_to_real(cordic_atan_out);
                error = $abs(actual_val - expected_val);

                $display("  Input: x=%f, y=%f", x_real, y_real);
                $display("  Expected: %f (0x%020x)", expected_val, expected);
                $display("  Actual:   %f (0x%020x)", actual_val, cordic_atan_out);
                $display("  Error:    %e", error);

                // Check if within reasonable tolerance (< 0.001%)
                if (error < $abs(expected_val) * 0.00001 || error < 1e-15) begin
                    $display("  PASS");
                    pass_count = pass_count + 1;
                end else begin
                    $display("  FAIL: Error too large");
                    fail_count = fail_count + 1;
                end
            end

            #100;
        end
    endtask

    task test_tan;
        input [79:0] angle;
        input [79:0] expected;
        input string test_name;
        real angle_val, expected_val, actual_val, error;
        begin
            test_num = test_num + 1;
            $display("Test %0d: TAN %s", test_num, test_name);

            angle_val = fp80_to_real(angle);
            expected_val = fp80_to_real(expected);

            @(posedge clk);
            cordic_enable = 1'b1;
            cordic_mode = MODE_TAN;
            cordic_angle_in = angle;

            @(posedge clk);
            cordic_enable = 1'b0;

            // Wait for completion (with timeout)
            fork
                wait(cordic_done);
                begin
                    #500000;  // 500 us timeout
                    $display("  TIMEOUT!");
                end
            join_any
            disable fork;

            if (!cordic_done) begin
                $display("  FAIL: Operation timed out");
                fail_count = fail_count + 1;
            end else if (cordic_error) begin
                $display("  FAIL: Error flag set");
                fail_count = fail_count + 1;
            end else begin
                actual_val = fp80_to_real(cordic_tan_out);
                error = $abs(actual_val - expected_val);

                $display("  Input angle: %f rad (0x%020x)", angle_val, angle);
                $display("  Expected: %f (0x%020x)", expected_val, expected);
                $display("  Actual:   %f (0x%020x)", actual_val, cordic_tan_out);
                $display("  Error:    %e", error);

                // Check if within reasonable tolerance
                if (error < $abs(expected_val) * 0.00001 || error < 1e-15) begin
                    $display("  PASS");
                    pass_count = pass_count + 1;
                end else begin
                    $display("  FAIL: Error too large");
                    fail_count = fail_count + 1;
                end
            end

            #100;
        end
    endtask

    //=================================================================
    // Main test sequence
    //=================================================================

    initial begin
        $display("========================================");
        $display("CORDIC Integration Test with Real Arithmetic Units");
        $display("Plan 2: Heavy Unit Reuse Implementation");
        $display("========================================");

        // Initialize
        reset = 1;
        cordic_enable = 0;
        cordic_mode = 0;
        cordic_angle_in = 0;
        cordic_x_in = 0;
        cordic_y_in = 0;
        test_num = 0;
        pass_count = 0;
        fail_count = 0;

        #100;
        reset = 0;
        #20;

        $display("\n--- ATAN Tests (MODE_VECTORING with correction) ---\n");

        // Test 1: atan(1/1) = π/4 ≈ 0.785398
        test_atan(
            FP80_ONE,   // x = 1.0
            FP80_ONE,   // y = 1.0
            FP80_PI_DIV_4,
            "atan(1.0/1.0) = π/4"
        );

        // Test 2: atan(0/1) = 0
        test_atan(
            FP80_ONE,   // x = 1.0
            FP80_ZERO,  // y = 0.0
            FP80_ZERO,
            "atan(0.0/1.0) = 0"
        );

        // Test 3: atan(√3/1) = π/3 ≈ 1.047198
        // √3 ≈ 1.732050808 = 0x3FFF_DDB3D742C265539F
        test_atan(
            FP80_ONE,                           // x = 1.0
            80'h3FFF_DDB3D742C265539F,         // y = √3
            80'h3FFF_860A91C16B9B2C23,         // π/3
            "atan(√3/1) ≈ π/3"
        );

        // Test 4: atan(1/√3) = π/6 ≈ 0.523599
        test_atan(
            80'h3FFF_DDB3D742C265539F,         // x = √3
            FP80_ONE,                           // y = 1.0
            FP80_PI_DIV_6,
            "atan(1/√3) = π/6"
        );

        $display("\n--- TAN Tests (MODE_TAN with correction) ---\n");

        // Test 5: tan(0) = 0
        test_tan(
            FP80_ZERO,
            FP80_ZERO,
            "tan(0) = 0"
        );

        // Test 6: tan(π/4) = 1
        test_tan(
            FP80_PI_DIV_4,
            FP80_ONE,
            "tan(π/4) = 1"
        );

        // Test 7: tan(π/6) ≈ 0.577350 = 1/√3
        // 1/√3 = 0x3FFE_93C467E37DB0C7A5
        test_tan(
            FP80_PI_DIV_6,
            80'h3FFE_93C467E37DB0C7A5,
            "tan(π/6) ≈ 0.577350"
        );

        // Test 8: Small angle (2^-10 ≈ 0.0009766)
        // tan(x) ≈ x for small x
        test_tan(
            80'h3FF6_8000000000000000,  // 2^-10
            80'h3FF6_8000000000000000,  // ≈ 2^-10 (tan(x)≈x for small x)
            "tan(2^-10) ≈ 2^-10 (small angle)"
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
        #5000000;  // 5 ms total timeout
        $display("ERROR: Global test timeout!");
        $finish(2);
    end

endmodule
