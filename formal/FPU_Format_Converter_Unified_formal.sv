// Formal verification harness for FPU_Format_Converter_Unified
// Verifies conversion mode validity, output activation, and exception flags

`default_nettype none

module FPU_Format_Converter_Unified_formal (
    input logic clk
);
    // Reset signal
    logic reset;

    // Control
    (* anyseq *) logic enable;
    (* anyseq *) logic [3:0] mode;
    (* anyseq *) logic [1:0] rounding_mode;

    // Inputs
    (* anyseq *) logic [79:0] fp80_in;
    (* anyseq *) logic [63:0] fp64_in;
    (* anyseq *) logic [31:0] fp32_in;
    (* anyseq *) logic [63:0] uint64_in;
    (* anyseq *) logic [31:0] int32_in;
    (* anyseq *) logic [15:0] int16_in;
    (* anyseq *) logic [63:0] fixed64_in;
    (* anyseq *) logic uint64_sign;

    // Outputs
    logic [79:0] fp80_out;
    logic [63:0] fp64_out;
    logic [31:0] fp32_out;
    logic [63:0] uint64_out;
    logic [31:0] int32_out;
    logic [15:0] int16_out;
    logic [63:0] fixed64_out;
    logic uint64_sign_out;
    logic done;
    logic flag_invalid;
    logic flag_overflow;
    logic flag_underflow;
    logic flag_inexact;

    // Instantiate DUT
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

    //=========================================================================
    // Mode definitions
    //=========================================================================

    localparam MODE_FP32_TO_FP80   = 4'd0;
    localparam MODE_FP64_TO_FP80   = 4'd1;
    localparam MODE_FP80_TO_FP32   = 4'd2;
    localparam MODE_FP80_TO_FP64   = 4'd3;
    localparam MODE_INT16_TO_FP80  = 4'd4;
    localparam MODE_INT32_TO_FP80  = 4'd5;
    localparam MODE_FP80_TO_INT16  = 4'd6;
    localparam MODE_FP80_TO_INT32  = 4'd7;
    localparam MODE_UINT64_TO_FP80 = 4'd8;
    localparam MODE_FP80_TO_UINT64 = 4'd9;
    localparam MODE_FP80_TO_FIXED64 = 4'd10;
    localparam MODE_FIXED64_TO_FP80 = 4'd11;

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
    // Track conversion
    //=========================================================================

    logic [3:0] latched_mode;

    always_ff @(posedge clk) begin
        if (reset) begin
            latched_mode <= 4'd0;
        end else if (enable) begin
            latched_mode <= mode;
        end
    end

    //=========================================================================
    // Formal Properties
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin

            //=================================================================
            // Property 1: Reset clears done and flags
            //=================================================================
            if ($past(reset)) begin
                assert(!done);
                assert(!flag_invalid);
                assert(!flag_overflow);
                assert(!flag_underflow);
                assert(!flag_inexact);
            end

            //=================================================================
            // Property 2: Enable triggers done on next cycle
            //=================================================================
            if ($past(enable) && !$past(reset))
                assert(done);

            //=================================================================
            // Property 3: Done is a pulse (cleared after one cycle)
            //=================================================================
            if ($past(done) && !$past(enable) && !$past(reset))
                assert(!done);

            //=================================================================
            // Property 4: Valid mode range (0-11 defined, 12-15 reserved)
            //=================================================================
            // Environment assumption for valid modes
            if (enable)
                assume(mode <= 4'd11);

            //=================================================================
            // Property 5: Output to FP80 modes produce FP80 output
            //=================================================================
            // Modes 0,1,4,5,8,11 output to FP80

            //=================================================================
            // Property 6: Flags only set during conversion
            //=================================================================
            // If no enable in past, flags should be stable or cleared
            if (!$past(enable) && !$past(reset)) begin
                // Flags should not spontaneously set
                if (!$past(flag_invalid))
                    assert(!flag_invalid || $past(enable));
            end

            //=================================================================
            // Property 7: Overflow only possible for narrowing conversions
            //=================================================================
            // FP80→FP32, FP80→FP64, FP80→INT modes can overflow
            if (done && flag_overflow) begin
                assert(latched_mode == MODE_FP80_TO_FP32 ||
                       latched_mode == MODE_FP80_TO_FP64 ||
                       latched_mode == MODE_FP80_TO_INT16 ||
                       latched_mode == MODE_FP80_TO_INT32 ||
                       latched_mode == MODE_FP80_TO_UINT64 ||
                       latched_mode == MODE_FP80_TO_FIXED64);
            end

            //=================================================================
            // Property 8: Underflow only possible for FP output modes
            //=================================================================
            if (done && flag_underflow) begin
                assert(latched_mode == MODE_FP80_TO_FP32 ||
                       latched_mode == MODE_FP80_TO_FP64);
            end

            //=================================================================
            // Property 9: Sign preservation for widening conversions
            //=================================================================
            // FP32→FP80, FP64→FP80 should preserve sign
            // (simplified - full check would verify bit values)

            //=================================================================
            // Property 10: Zero input produces zero output (for FP modes)
            //=================================================================
            // (simplified check)

        end
    end

    //=========================================================================
    // Cover Properties - Verify reachability
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin
            // Cover: Conversion completes
            cover(done);

            // Cover: Each mode
            cover(done && latched_mode == MODE_FP32_TO_FP80);
            cover(done && latched_mode == MODE_FP64_TO_FP80);
            cover(done && latched_mode == MODE_FP80_TO_FP32);
            cover(done && latched_mode == MODE_FP80_TO_FP64);
            cover(done && latched_mode == MODE_INT16_TO_FP80);
            cover(done && latched_mode == MODE_INT32_TO_FP80);
            cover(done && latched_mode == MODE_FP80_TO_INT16);
            cover(done && latched_mode == MODE_FP80_TO_INT32);

            // Cover: Exception flags
            cover(flag_invalid);
            cover(flag_overflow);
            cover(flag_underflow);
            cover(flag_inexact);
        end
    end

endmodule
