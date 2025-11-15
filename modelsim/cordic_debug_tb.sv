`timescale 1ns / 1ps

//=====================================================================
// Simplified CORDIC Debug Testbench
//
// Focuses on debugging accuracy issues with detailed logging and
// waveform dumping.
//=====================================================================

module cordic_debug_tb;

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

    // MulDiv unit
    reg        muldiv_enable;
    reg        muldiv_operation;
    reg [79:0] muldiv_operand_a;
    reg [79:0] muldiv_operand_b;
    wire [79:0] muldiv_result;
    wire        muldiv_done;
    wire        muldiv_flag_invalid;

    // Test parameters
    localparam MODE_ROTATION  = 2'b00;
    localparam MODE_VECTORING = 2'b01;
    localparam MODE_TAN       = 2'b10;

    // FP80 constants
    localparam FP80_ZERO = 80'h0000_0000000000000000;
    localparam FP80_ONE  = 80'h3FFF_8000000000000000;

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
        .rounding_mode(2'b00),
        .result(addsub_result),
        .done(addsub_done),
        .cmp_equal(),
        .cmp_less(),
        .cmp_greater(),
        .flag_invalid(addsub_flag_invalid),
        .flag_overflow(),
        .flag_underflow(),
        .flag_inexact()
    );

    FPU_IEEE754_MulDiv_Unified muldiv_unit (
        .clk(clk),
        .reset(reset),
        .enable(muldiv_enable),
        .operation(muldiv_operation),
        .operand_a(muldiv_operand_a),
        .operand_b(muldiv_operand_b),
        .rounding_mode(2'b00),
        .result(muldiv_result),
        .done(muldiv_done),
        .flag_invalid(muldiv_flag_invalid),
        .flag_div_by_zero(),
        .flag_overflow(),
        .flag_underflow(),
        .flag_inexact()
    );

    //=================================================================
    // Arbiter with Debug Logging
    //=================================================================

    integer arith_op_count;

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

            arith_op_count = 0;
        end else begin
            // AddSub request handling
            if (cordic_addsub_req && !addsub_enable) begin
                addsub_enable <= 1'b1;
                addsub_operand_a <= cordic_addsub_a;
                addsub_operand_b <= cordic_addsub_b;
                addsub_subtract <= cordic_addsub_sub;
                cordic_addsub_done <= 1'b0;

                arith_op_count = arith_op_count + 1;
                $display("[%0t] AddSub Op#%0d: %s", $time, arith_op_count,
                         cordic_addsub_sub ? "SUB" : "ADD");
                $display("  A = 0x%020x", cordic_addsub_a);
                $display("  B = 0x%020x", cordic_addsub_b);
            end else if (addsub_enable && !cordic_addsub_req) begin
                addsub_enable <= 1'b0;
            end

            // AddSub result
            if (addsub_done) begin
                cordic_addsub_result <= addsub_result;
                cordic_addsub_done <= 1'b1;
                cordic_addsub_invalid <= addsub_flag_invalid;

                $display("  Result = 0x%020x (invalid=%b)", addsub_result, addsub_flag_invalid);
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

                arith_op_count = arith_op_count + 1;
                $display("[%0t] MulDiv Op#%0d: %s", $time, arith_op_count,
                         cordic_muldiv_op ? "DIV" : "MUL");
                $display("  A = 0x%020x", cordic_muldiv_a);
                $display("  B = 0x%020x", cordic_muldiv_b);
            end else if (muldiv_enable && !cordic_muldiv_req) begin
                muldiv_enable <= 1'b0;
            end

            // MulDiv result
            if (muldiv_done) begin
                cordic_muldiv_result <= muldiv_result;
                cordic_muldiv_done <= 1'b1;
                cordic_muldiv_invalid <= muldiv_flag_invalid;

                $display("  Result = 0x%020x (invalid=%b)", muldiv_result, muldiv_flag_invalid);
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
        forever #5 clk = ~clk;  // 100 MHz
    end

    //=================================================================
    // State monitoring
    //=================================================================

    reg [4:0] prev_state;

    always @(posedge clk) begin
        if (reset) begin
            prev_state <= 5'd0;
        end else begin
            if (cordic_dut.state != prev_state) begin  // State changed
                prev_state <= cordic_dut.state;
                case (cordic_dut.state)
                    5'd0: $display("[%0t] State: IDLE", $time);
                    5'd1: $display("[%0t] State: RANGE_REDUCE", $time);
                    5'd2: $display("[%0t] State: CONVERT_INPUT", $time);
                    5'd3: $display("[%0t] State: CORDIC_INIT", $time);
                    5'd4: $display("[%0t] State: CORDIC_ITER (iter=%0d)", $time, cordic_dut.iteration_count);
                    5'd5: $display("[%0t] State: CONVERT_OUTPUT", $time);
                    5'd6: $display("[%0t] State: QUAD_CORRECT", $time);
                    5'd7: $display("[%0t] State: DONE", $time);
                    5'd8: $display("[%0t] State: CORR_CALC_RESIDUAL", $time);
                    5'd9: $display("[%0t] State: CORR_WAIT_RESIDUAL", $time);
                    5'd10: $display("[%0t] State: CORR_MUL_E2", $time);
                    5'd11: $display("[%0t] State: CORR_WAIT_MUL_E2", $time);
                    5'd12: $display("[%0t] State: CORR_MUL_C3", $time);
                    5'd13: $display("[%0t] State: CORR_WAIT_MUL_C3", $time);
                    5'd14: $display("[%0t] State: CORR_ADD_C1", $time);
                    5'd15: $display("[%0t] State: CORR_WAIT_ADD", $time);
                    5'd16: $display("[%0t] State: CORR_MUL_E", $time);
                    5'd17: $display("[%0t] State: CORR_WAIT_MUL_E", $time);
                    5'd18: $display("[%0t] State: CORR_COMBINE", $time);
                    5'd19: $display("[%0t] State: CORR_WAIT_COMBINE", $time);
                    default: $display("[%0t] State: UNKNOWN (%0d)", $time, cordic_dut.state);
                endcase
            end
        end
    end

    //=================================================================
    // Main test
    //=================================================================

    initial begin
        $dumpfile("cordic_debug.vcd");
        $dumpvars(0, cordic_debug_tb);

        $display("========================================");
        $display("CORDIC Debug Testbench");
        $display("========================================\n");

        // Initialize
        reset = 1;
        cordic_enable = 0;
        cordic_mode = 0;
        cordic_angle_in = 0;
        cordic_x_in = 0;
        cordic_y_in = 0;

        #100;
        reset = 0;
        #20;

        // Test 1: Simple ATAN(1,1) = π/4
        $display("\n========================================");
        $display("Test: ATAN(1.0, 1.0) should = π/4");
        $display("========================================");

        @(posedge clk);
        cordic_enable = 1'b1;
        cordic_mode = MODE_VECTORING;
        cordic_x_in = FP80_ONE;
        cordic_y_in = FP80_ONE;

        $display("Input: x = 0x%020x (1.0)", FP80_ONE);
        $display("Input: y = 0x%020x (1.0)", FP80_ONE);

        @(posedge clk);
        cordic_enable = 1'b0;

        // Wait for done
        wait(cordic_done);

        #100;

        $display("\n========================================");
        $display("Test Results:");
        $display("========================================");
        $display("ATAN output  = 0x%020x", cordic_atan_out);
        $display("Expected π/4 = 0x3FFEC90FDAA22168C235");
        $display("Error flag   = %b", cordic_error);

        // Check internal registers for debugging
        $display("\nInternal State:");
        $display("  x_cordic = 0x%016x", cordic_dut.x_cordic);
        $display("  y_cordic = 0x%016x", cordic_dut.y_cordic);
        $display("  z_cordic = 0x%016x", cordic_dut.z_cordic);
        $display("  residual_angle = 0x%020x", cordic_dut.residual_angle);
        $display("  epsilon_squared = 0x%020x", cordic_dut.epsilon_squared);
        $display("  correction_value = 0x%020x", cordic_dut.correction_value);
        $display("  cordic_partial_result = 0x%020x", cordic_dut.cordic_partial_result);

        #100;

        $display("\n========================================");
        $display("Test Complete");
        $display("========================================");

        $finish(0);
    end

    // Timeout watchdog
    initial begin
        #1000000;  // 1 ms timeout
        $display("ERROR: Test timeout!");
        $finish(2);
    end

endmodule
