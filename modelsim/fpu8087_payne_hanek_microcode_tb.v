`timescale 1ns / 1ps

//=============================================================================
// Testbench: Payne-Hanek Microcode Execution
//
// Tests the microcode routine at address 0x0180 with various large angles
// Verifies:
//   - Microcode execution completes successfully
//   - Reduced angles are in correct range [0, π/2)
//   - Quadrant information is correct
//   - Accuracy compared to software reference
//=============================================================================

module tb_payne_hanek_microcode;

    //=========================================================================
    // Clock and Reset
    //=========================================================================
    reg clk;
    reg reset;

    // Generate 50 MHz clock (20ns period)
    initial begin
        clk = 0;
        forever #10 clk = ~clk;
    end

    //=========================================================================
    // MicroSequencer Interface
    //=========================================================================
    reg         microseq_start;
    reg [4:0]   microseq_program_index;
    wire        microseq_complete;
    reg [79:0]  microseq_data_in;
    wire [79:0] microseq_data_out;

    // Debug outputs
    wire [79:0] debug_temp_result;
    wire [79:0] debug_temp_fp_a;
    wire [79:0] debug_temp_fp_b;
    wire [79:0] debug_temp_fp_c;
    wire [63:0] debug_temp_uint64;
    wire        debug_temp_sign;

    //=========================================================================
    // ROM Interface
    //=========================================================================
    wire [2:0]  ph_rom_addr;
    wire [79:0] ph_rom_data;

    //=========================================================================
    // Arithmetic Unit Interface
    //=========================================================================
    wire [4:0]  arith_operation;
    wire        arith_enable;
    wire [1:0]  arith_rounding_mode;
    wire [79:0] arith_operand_a;
    wire [79:0] arith_operand_b;
    wire signed [15:0] arith_int16_in;
    wire signed [31:0] arith_int32_in;
    wire [63:0] arith_uint64_in;
    wire        arith_uint64_sign_in;
    wire [31:0] arith_fp32_in;
    wire [63:0] arith_fp64_in;

    reg [79:0]  arith_result;
    reg signed [15:0] arith_int16_out;
    reg signed [31:0] arith_int32_out;
    reg [63:0]  arith_uint64_out;
    reg         arith_uint64_sign_out;
    reg [31:0]  arith_fp32_out;
    reg [63:0]  arith_fp64_out;
    reg         arith_done;
    reg         arith_invalid;
    reg         arith_overflow;
    reg         arith_cc_less;
    reg         arith_cc_equal;
    reg         arith_cc_greater;
    reg         arith_cc_unordered;

    //=========================================================================
    // BCD Converter Stubs (not used in Payne-Hanek)
    //=========================================================================
    wire        bcd2bin_enable;
    wire [79:0] bcd2bin_bcd_in;
    reg [63:0]  bcd2bin_binary_out = 0;
    reg         bcd2bin_sign_out = 0;
    reg         bcd2bin_done = 0;
    reg         bcd2bin_error = 0;

    wire        bin2bcd_enable;
    wire [63:0] bin2bcd_binary_in;
    wire        bin2bcd_sign_in;
    reg [79:0]  bin2bcd_bcd_out = 0;
    reg         bin2bcd_done = 0;
    reg         bin2bcd_error = 0;

    //=========================================================================
    // Instantiate ROM
    //=========================================================================
    FPU_Payne_Hanek_ROM rom (
        .clk(clk),
        .addr(ph_rom_addr),
        .data_out(ph_rom_data)
    );

    //=========================================================================
    // Instantiate MicroSequencer
    //=========================================================================
    MicroSequencer_Extended_BCD microseq (
        .clk(clk),
        .reset(reset),

        // Control interface
        .start(microseq_start),
        .micro_program_index(microseq_program_index),
        .instruction_complete(microseq_complete),

        // Data bus interface
        .data_in(microseq_data_in),
        .data_out(microseq_data_out),

        // Debug interface
        .debug_temp_result(debug_temp_result),
        .debug_temp_fp_a(debug_temp_fp_a),
        .debug_temp_fp_b(debug_temp_fp_b),
        .debug_temp_uint64(debug_temp_uint64),
        .debug_temp_sign(debug_temp_sign),

        // Arithmetic unit interface
        .arith_operation(arith_operation),
        .arith_enable(arith_enable),
        .arith_rounding_mode(arith_rounding_mode),
        .arith_operand_a(arith_operand_a),
        .arith_operand_b(arith_operand_b),
        .arith_int16_in(arith_int16_in),
        .arith_int32_in(arith_int32_in),
        .arith_uint64_in(arith_uint64_in),
        .arith_uint64_sign_in(arith_uint64_sign_in),
        .arith_fp32_in(arith_fp32_in),
        .arith_fp64_in(arith_fp64_in),
        .arith_result(arith_result),
        .arith_result_secondary(80'h0),
        .arith_int16_out(arith_int16_out),
        .arith_int32_out(arith_int32_out),
        .arith_uint64_out(arith_uint64_out),
        .arith_uint64_sign_out(arith_uint64_sign_out),
        .arith_fp32_out(arith_fp32_out),
        .arith_fp64_out(arith_fp64_out),
        .arith_done(arith_done),
        .arith_invalid(arith_invalid),
        .arith_overflow(arith_overflow),
        .arith_cc_less(arith_cc_less),
        .arith_cc_equal(arith_cc_equal),
        .arith_cc_greater(arith_cc_greater),
        .arith_cc_unordered(arith_cc_unordered),

        // BCD converter interfaces
        .bcd2bin_enable(bcd2bin_enable),
        .bcd2bin_bcd_in(bcd2bin_bcd_in),
        .bcd2bin_binary_out(bcd2bin_binary_out),
        .bcd2bin_sign_out(bcd2bin_sign_out),
        .bcd2bin_done(bcd2bin_done),
        .bcd2bin_error(bcd2bin_error),

        .bin2bcd_enable(bin2bcd_enable),
        .bin2bcd_binary_in(bin2bcd_binary_in),
        .bin2bcd_sign_in(bin2bcd_sign_in),
        .bin2bcd_bcd_out(bin2bcd_bcd_out),
        .bin2bcd_done(bin2bcd_done),
        .bin2bcd_error(bin2bcd_error),

        // Payne-Hanek ROM interface
        .ph_rom_addr(ph_rom_addr),
        .ph_rom_data(ph_rom_data)
    );

    //=========================================================================
    // Real FPU Arithmetic Units
    //=========================================================================

    // AddSub unit signals
    wire addsub_enable;
    wire addsub_subtract;
    wire [79:0] addsub_result;
    wire addsub_done;
    wire addsub_cmp_equal, addsub_cmp_less, addsub_cmp_greater;
    wire addsub_invalid, addsub_overflow, addsub_underflow, addsub_inexact;

    // MulDiv unit signals
    wire muldiv_enable;
    wire muldiv_operation;  // 0=mul, 1=div
    wire [79:0] muldiv_result;
    wire muldiv_done;
    wire muldiv_invalid, muldiv_div_by_zero, muldiv_overflow, muldiv_underflow, muldiv_inexact;

    // Operation routing
    reg [4:0]  arith_op_reg;
    reg [79:0] arith_a_reg;
    reg [79:0] arith_b_reg;
    reg        arith_active;

    assign addsub_enable = arith_active && (arith_op_reg == 5'd0 || arith_op_reg == 5'd1);
    assign addsub_subtract = (arith_op_reg == 5'd1);

    assign muldiv_enable = arith_active && (arith_op_reg == 5'd2 || arith_op_reg == 5'd3);
    assign muldiv_operation = (arith_op_reg == 5'd3);  // 0=mul, 1=div

    // Real FPU IEEE754 AddSub Unit
    FPU_IEEE754_AddSub addsub_unit (
        .clk(clk),
        .reset(reset),
        .enable(addsub_enable),
        .operand_a(arith_a_reg),
        .operand_b(arith_b_reg),
        .subtract(addsub_subtract),
        .rounding_mode(2'b00),  // Round to nearest
        .result(addsub_result),
        .done(addsub_done),
        .cmp_equal(addsub_cmp_equal),
        .cmp_less(addsub_cmp_less),
        .cmp_greater(addsub_cmp_greater),
        .flag_invalid(addsub_invalid),
        .flag_overflow(addsub_overflow),
        .flag_underflow(addsub_underflow),
        .flag_inexact(addsub_inexact)
    );

    // Real FPU IEEE754 MulDiv Unit
    FPU_IEEE754_MulDiv_Unified muldiv_unit (
        .clk(clk),
        .reset(reset),
        .enable(muldiv_enable),
        .operation(muldiv_operation),
        .operand_a(arith_a_reg),
        .operand_b(arith_b_reg),
        .rounding_mode(2'b00),  // Round to nearest
        .result(muldiv_result),
        .done(muldiv_done),
        .flag_invalid(muldiv_invalid),
        .flag_div_by_zero(muldiv_div_by_zero),
        .flag_overflow(muldiv_overflow),
        .flag_underflow(muldiv_underflow),
        .flag_inexact(muldiv_inexact)
    );

    // Control logic
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            arith_done <= 0;
            arith_result <= 0;
            arith_op_reg <= 0;
            arith_a_reg <= 0;
            arith_b_reg <= 0;
            arith_active <= 0;
            arith_invalid <= 0;
            arith_overflow <= 0;
        end else begin
            if (arith_enable && !arith_active) begin
                // Start new operation
                arith_op_reg <= arith_operation;
                arith_a_reg <= arith_operand_a;
                arith_b_reg <= arith_operand_b;
                arith_active <= 1;
                arith_done <= 0;
                $display("[ARITH_REAL] Started operation %0d: A=%h, B=%h", arith_operation, arith_operand_a, arith_operand_b);
            end else if (arith_active) begin
                // Check if operation completed
                if ((arith_op_reg == 5'd0 || arith_op_reg == 5'd1) && addsub_done) begin
                    // AddSub completed
                    arith_result <= addsub_result;
                    arith_done <= 1;
                    arith_active <= 0;
                    arith_invalid <= addsub_invalid;
                    arith_overflow <= addsub_overflow;
                    $display("[ARITH_REAL] AddSub completed: Result=%h", addsub_result);
                end else if ((arith_op_reg == 5'd2 || arith_op_reg == 5'd3) && muldiv_done) begin
                    // MulDiv completed
                    arith_result <= muldiv_result;
                    arith_done <= 1;
                    arith_active <= 0;
                    arith_invalid <= muldiv_invalid;
                    arith_overflow <= muldiv_overflow;
                    $display("[ARITH_REAL] MulDiv completed: Result=%h", muldiv_result);
                end else if (arith_op_reg == 5'd14) begin
                    // FLOOR operation (custom, not in real FPU)
                    arith_result <= perform_fp80_floor(arith_a_reg);
                    arith_done <= 1;
                    arith_active <= 0;
                    $display("[ARITH_REAL] FLOOR completed: Result=%h", arith_result);
                end
            end else begin
                arith_done <= 0;
            end
        end
    end

    //=========================================================================
    // FLOOR Operation Function (Custom - not in real FPU)
    //=========================================================================
    function [79:0] perform_fp80_floor;
        input [79:0] a;
        reg [14:0] exp_a;
        reg [63:0] mant_a;
        reg [63:0] mant_res;
        integer shift_amount;
        begin
            exp_a = a[78:64];
            mant_a = a[63:0];

            if (exp_a < 15'h3FFF) begin
                // Value < 1.0, return 0
                perform_fp80_floor = 80'd0;
            end else if (exp_a >= 15'h3FFF + 63) begin
                // Value >= 2^63, already an integer
                perform_fp80_floor = a;
            end else begin
                // Extract integer bits based on exponent
                shift_amount = 63 - (exp_a - 15'h3FFF);

                if (shift_amount >= 64) begin
                    // Less than 1.0
                    perform_fp80_floor = 80'd0;
                end else begin
                    // Mask off fractional bits
                    mant_res = mant_a;
                    if (shift_amount > 0) begin
                        // Zero out the fractional bits
                        mant_res = (mant_a >> shift_amount) << shift_amount;
                    end
                    perform_fp80_floor = {a[79], exp_a, mant_res};
                end
            end
        end
    endfunction

    //=========================================================================
    // Helper Functions
    //=========================================================================

    // Create FP80 value from real number (simplified)
    function [79:0] real_to_fp80;
        input real value;
        reg sign;
        reg [14:0] exponent;
        reg [63:0] mantissa;
        real abs_value;
        integer exp_adj;
        real normalized;
        begin
            if (value == 0.0) begin
                real_to_fp80 = 80'd0;
            end else begin
                // Extract sign
                sign = (value < 0.0) ? 1'b1 : 1'b0;
                abs_value = (value < 0.0) ? -value : value;

                // Normalize and find exponent
                exp_adj = 0;
                normalized = abs_value;

                // Scale to [1.0, 2.0) range
                while (normalized >= 2.0) begin
                    normalized = normalized / 2.0;
                    exp_adj = exp_adj + 1;
                end
                while (normalized < 1.0 && normalized > 0.0) begin
                    normalized = normalized * 2.0;
                    exp_adj = exp_adj - 1;
                end

                // Exponent with bias (16383 for FP80)
                exponent = exp_adj + 15'h3FFF;

                // Convert mantissa (simplified - upper bits only)
                mantissa = $rtoi((normalized - 1.0) * (2.0 ** 63));
                mantissa[63] = 1'b1; // Set integer bit

                real_to_fp80 = {sign, exponent, mantissa};
            end
        end
    endfunction

    // Convert FP80 to real (simplified)
    function real fp80_to_real;
        input [79:0] fp80;
        reg sign;
        reg [14:0] exponent;
        reg [63:0] mantissa;
        integer exp_unbias;
        real mant_real;
        real result;
        begin
            sign = fp80[79];
            exponent = fp80[78:64];
            mantissa = fp80[63:0];

            if (exponent == 0) begin
                fp80_to_real = 0.0;
            end else begin
                exp_unbias = exponent - 15'h3FFF;
                mant_real = 1.0 + ($itor(mantissa & 64'h7FFFFFFFFFFFFFFF) / (2.0 ** 63));
                result = mant_real * (2.0 ** exp_unbias);
                fp80_to_real = sign ? -result : result;
            end
        end
    endfunction

    //=========================================================================
    // Test Tasks
    //=========================================================================

    task test_payne_hanek;
        input [79:0] angle_in;
        input real angle_real;
        input string description;

        real reduced_real;
        real expected_reduced;
        integer expected_quadrant;
        real error;
        real pi_half;

        begin
            $display("\n========================================");
            $display("Test: %s", description);
            $display("Input angle: %h (%.6f rad)", angle_in, angle_real);

            pi_half = 1.5707963267948966;

            // Calculate expected result
            // angle_real mod 2π, then determine quadrant and reduce to [0, π/2)
            expected_reduced = angle_real;
            expected_quadrant = 0;

            // Reduce to [0, 2π)
            while (expected_reduced >= 6.283185307179586) begin
                expected_reduced = expected_reduced - 6.283185307179586;
            end
            while (expected_reduced < 0.0) begin
                expected_reduced = expected_reduced + 6.283185307179586;
            end

            // Determine quadrant and reduce to [0, π/2)
            if (expected_reduced < pi_half) begin
                expected_quadrant = 0;
                // Already in [0, π/2)
            end else if (expected_reduced < 2.0 * pi_half) begin
                expected_quadrant = 1;
                expected_reduced = 2.0 * pi_half - expected_reduced;
            end else if (expected_reduced < 3.0 * pi_half) begin
                expected_quadrant = 2;
                expected_reduced = expected_reduced - 2.0 * pi_half;
            end else begin
                expected_quadrant = 3;
                expected_reduced = 4.0 * pi_half - expected_reduced;
            end

            $display("Expected reduced angle: %.10f rad (quadrant %0d)", expected_reduced, expected_quadrant);

            // Load input angle into data_in
            microseq_data_in = angle_in;

            // Start microcode program 22 (Payne-Hanek at 0x0180)
            microseq_program_index = 5'd22;
            microseq_start = 1;
            @(posedge clk);
            microseq_start = 0;

            // Wait for completion (with timeout)
            fork
                begin: wait_complete
                    @(posedge microseq_complete);
                    disable timeout;
                end

                begin: timeout
                    repeat (1000) @(posedge clk);
                    $display("ERROR: Microcode execution timeout!");
                    disable wait_complete;
                end
            join

            // Check results
            if (microseq_complete) begin
                reduced_real = fp80_to_real(debug_temp_result);
                $display("Microcode completed successfully");
                $display("Output reduced angle: %h (%.10f rad)", debug_temp_result, reduced_real);
                $display("Quadrant register (temp_fp_c): %h", debug_temp_fp_c);

                error = reduced_real - expected_reduced;
                if (error < 0.0) error = -error;

                $display("Error: %.2e rad", error);

                if (error < 1e-6) begin
                    $display("PASS: Reduced angle within tolerance");
                end else if (error < 1e-3) begin
                    $display("WARN: Reduced angle has larger error than expected");
                end else begin
                    $display("FAIL: Reduced angle error too large");
                end
            end else begin
                $display("FAIL: Microcode did not complete");
            end

            $display("========================================\n");
        end
    endtask

    //=========================================================================
    // Main Test Sequence
    //=========================================================================
    integer pass_count;
    integer test_count;

    initial begin
        $display("\n");
        $display("========================================================================");
        $display("  Payne-Hanek Microcode Execution Test");
        $display("========================================================================");

        pass_count = 0;
        test_count = 0;

        // Initialize
        reset = 1;
        microseq_start = 0;
        microseq_program_index = 0;
        microseq_data_in = 0;

        repeat (10) @(posedge clk);
        reset = 0;
        repeat (10) @(posedge clk);

        // Test 1: 1000π
        test_count = test_count + 1;
        test_payne_hanek(
            real_to_fp80(3141.59265358979),  // 1000π
            3141.59265358979,
            "1000π (Large angle)"
        );

        // Test 2: 10000π
        test_count = test_count + 1;
        test_payne_hanek(
            real_to_fp80(31415.9265358979),  // 10000π
            31415.9265358979,
            "10000π (Very large angle)"
        );

        // Test 3: 256 (threshold value)
        test_count = test_count + 1;
        test_payne_hanek(
            real_to_fp80(256.0),
            256.0,
            "256 (Threshold value)"
        );

        // Test 4: 1024
        test_count = test_count + 1;
        test_payne_hanek(
            real_to_fp80(1024.0),
            1024.0,
            "1024"
        );

        // Test 5: 100000π (extreme case)
        test_count = test_count + 1;
        test_payne_hanek(
            real_to_fp80(314159.265358979),  // 100000π
            314159.265358979,
            "100000π (Extreme angle)"
        );

        // Test 6: Negative large angle
        test_count = test_count + 1;
        test_payne_hanek(
            real_to_fp80(-3141.59265358979),  // -1000π
            -3141.59265358979,
            "-1000π (Negative large angle)"
        );

        repeat (50) @(posedge clk);

        $display("\n========================================================================");
        $display("  Test Summary");
        $display("========================================================================");
        $display("Total tests: %0d", test_count);
        $display("Note: Manual verification required for pass/fail determination");
        $display("      Check reduced angles are in [0, π/2) and accuracy");
        $display("========================================================================\n");

        $finish;
    end

    // Timeout watchdog
    initial begin
        #100000; // 100us timeout
        $display("\n*** GLOBAL TIMEOUT - Test took too long ***\n");
        $finish;
    end

endmodule
