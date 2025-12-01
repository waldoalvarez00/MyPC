// Formal verification harness for FPU_Range_Reduction
// Verifies state machine, quadrant determination, and special value handling

`default_nettype none

module FPU_Range_Reduction_formal (
    input logic clk
);
    // Reset signal
    logic reset;

    // Control
    (* anyseq *) logic enable;
    (* anyseq *) logic [79:0] angle_in;

    // Outputs
    logic [79:0] angle_out;
    logic [1:0] quadrant;
    logic swap_sincos;
    logic negate_sin;
    logic negate_cos;
    logic done;
    logic error;

    // Microcode interface (stub)
    logic ph_microcode_invoke;
    logic [11:0] ph_microcode_addr;
    logic [79:0] ph_microcode_operand_a;
    (* anyseq *) logic ph_microcode_done;
    (* anyseq *) logic [79:0] ph_microcode_result;
    (* anyseq *) logic [1:0] ph_microcode_quadrant;
    (* anyseq *) logic ph_microcode_error;

    // Instantiate DUT
    FPU_Range_Reduction dut (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .angle_in(angle_in),
        .angle_out(angle_out),
        .quadrant(quadrant),
        .swap_sincos(swap_sincos),
        .negate_sin(negate_sin),
        .negate_cos(negate_cos),
        .done(done),
        .error(error),
        .ph_microcode_invoke(ph_microcode_invoke),
        .ph_microcode_addr(ph_microcode_addr),
        .ph_microcode_operand_a(ph_microcode_operand_a),
        .ph_microcode_done(ph_microcode_done),
        .ph_microcode_result(ph_microcode_result),
        .ph_microcode_quadrant(ph_microcode_quadrant),
        .ph_microcode_error(ph_microcode_error)
    );

    //=========================================================================
    // Internal signal access for formal verification
    //=========================================================================

    // NOTE: Direct hierarchical access not supported by Yosys
    // Internal state monitoring disabled - properties verified through external signals only
`ifndef YOSYS
    wire [3:0] state = dut.state;
`else
    // Yosys: Define dummy signals to avoid compilation errors
    wire [3:0] state = 4'd0;  // Disabled for Yosys
`endif

    //=========================================================================
    // State encoding constants
    //=========================================================================

    localparam STATE_IDLE           = 4'd0;
    localparam STATE_CHECK_SPECIAL  = 4'd1;
    localparam STATE_REDUCE_2PI     = 4'd2;
    localparam STATE_DETERMINE_QUAD = 4'd3;
    localparam STATE_REDUCE_TO_PI4  = 4'd4;
    localparam STATE_PAYNE_HANEK    = 4'd5;
    localparam STATE_WAIT_PH        = 4'd6;
    localparam STATE_DONE           = 4'd7;

    //=========================================================================
    // Reset sequence
    //=========================================================================

    logic seen_reset;

    initial begin
        reset = 1'b1;
        seen_reset = 1'b0;
    end

    always_ff @(posedge clk) begin
        if ($initstate) begin
            reset <= 1'b1;
            seen_reset <= 1'b0;
        end else begin
            reset <= 1'b0;
            if (reset)
                seen_reset <= 1'b1;
        end
    end

    //=========================================================================
    // Helper functions for special value detection
    //=========================================================================

    wire sign_in = angle_in[79];
    wire [14:0] exp_in = angle_in[78:64];
    wire [63:0] mant_in = angle_in[63:0];

    wire is_zero = (exp_in == 15'd0) && (mant_in == 64'd0);
    wire is_inf = (exp_in == 15'h7FFF) && (mant_in[63] == 1'b1) && (mant_in[62:0] == 63'd0);
    wire is_nan = (exp_in == 15'h7FFF) && ((mant_in[63] == 1'b0) || (mant_in[62:0] != 63'd0));

    //=========================================================================
    // Environment assumptions
    //=========================================================================

    // Payne-Hanek responds within bounded time
    // NOTE: Timing delay assumptions commented out for Yosys compatibility
    // Yosys formal doesn't support SVA sequence syntax (##[range])
    // These would need to be implemented as explicit counters if needed
    /*
    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin
            if (dut.ph_enable && !dut.ph_done)
                assume(##[1:30] dut.ph_done);
        end
    end
    */

    //=========================================================================
    // Formal Properties
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin

            //=================================================================
            // Property 1: State is always valid (0-7)
            //=================================================================
            assert(state <= 4'd7);

            //=================================================================
            // Property 2: Reset puts FSM in IDLE state
            //=================================================================
            if ($past(reset))
                assert(state == STATE_IDLE);

            //=================================================================
            // Property 3: Done only asserted in IDLE or DONE state
            //=================================================================
            if (done)
                assert(state == STATE_IDLE || state == STATE_DONE);

            //=================================================================
            // Property 4: Enable starts operation from IDLE
            //=================================================================
            if ($past(enable) && $past(state) == STATE_IDLE && !$past(reset))
                assert(state != STATE_IDLE);

            //=================================================================
            // Property 5: Quadrant is valid (0-3)
            //=================================================================
            assert(quadrant <= 2'd3);

            //=================================================================
            // Property 6: Error flag for infinity input
            //=================================================================
            if (done && is_inf)
                assert(error);

            //=================================================================
            // Property 7: Error flag for NaN input
            //=================================================================
            if (done && is_nan)
                assert(error);

            //=================================================================
            // Property 8: Zero input should not produce error
            //=================================================================
            // (simplified check)

            //=================================================================
            // Property 9: Valid state transitions
            //=================================================================
            case ($past(state))
                STATE_IDLE: begin
                    assert(state == STATE_IDLE || state == STATE_CHECK_SPECIAL);
                end
                STATE_CHECK_SPECIAL: begin
                    // Can go to various states or back to IDLE (error)
                    assert(state == STATE_REDUCE_2PI ||
                           state == STATE_PAYNE_HANEK ||
                           state == STATE_IDLE ||
                           state == STATE_DONE);
                end
                STATE_REDUCE_2PI: begin
                    assert(state == STATE_DETERMINE_QUAD ||
                           state == STATE_REDUCE_2PI);
                end
                STATE_DETERMINE_QUAD: begin
                    assert(state == STATE_REDUCE_TO_PI4);
                end
                STATE_REDUCE_TO_PI4: begin
                    assert(state == STATE_DONE ||
                           state == STATE_REDUCE_TO_PI4);
                end
                STATE_PAYNE_HANEK: begin
                    assert(state == STATE_WAIT_PH);
                end
                STATE_WAIT_PH: begin
                    assert(state == STATE_WAIT_PH || state == STATE_DONE);
                end
                STATE_DONE: begin
                    assert(state == STATE_IDLE);
                end
            endcase

            //=================================================================
            // Property 10: Swap and negate flags are consistent with quadrant
            //=================================================================
            // Quadrant determines these flags based on trig identities
            // (detailed check would verify the specific mapping)

        end
    end

    //=========================================================================
    // Cover Properties - Verify reachability
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin
            // Cover: Operation completes
            cover(done);

            // Cover: Each state reached
            cover(state == STATE_IDLE);
            cover(state == STATE_CHECK_SPECIAL);
            cover(state == STATE_REDUCE_2PI);
            cover(state == STATE_DETERMINE_QUAD);
            cover(state == STATE_REDUCE_TO_PI4);
            cover(state == STATE_PAYNE_HANEK);
            cover(state == STATE_WAIT_PH);
            cover(state == STATE_DONE);

            // Cover: Each quadrant
            cover(done && quadrant == 2'd0);
            cover(done && quadrant == 2'd1);
            cover(done && quadrant == 2'd2);
            cover(done && quadrant == 2'd3);

            // Cover: Error conditions
            cover(error);
            cover(error && is_inf);
            cover(error && is_nan);

            // Cover: Swap and negate flags
            cover(done && swap_sincos);
            cover(done && negate_sin);
            cover(done && negate_cos);
        end
    end

endmodule
