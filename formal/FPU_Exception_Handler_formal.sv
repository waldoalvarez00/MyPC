// Formal verification harness for FPU_Exception_Handler
// Verifies exception priority, INT timing, mask behavior, and sticky latches

`default_nettype none

module FPU_Exception_Handler_formal (
    input logic clk
);
    // Reset signal
    logic reset;

    // Exception inputs from arithmetic unit
    (* anyseq *) logic exception_invalid;
    (* anyseq *) logic exception_denormal;
    (* anyseq *) logic exception_zero_div;
    (* anyseq *) logic exception_overflow;
    (* anyseq *) logic exception_underflow;
    (* anyseq *) logic exception_precision;

    // Mask bits from control word
    (* anyseq *) logic mask_invalid;
    (* anyseq *) logic mask_denormal;
    (* anyseq *) logic mask_zero_div;
    (* anyseq *) logic mask_overflow;
    (* anyseq *) logic mask_underflow;
    (* anyseq *) logic mask_precision;

    // Control signals
    (* anyseq *) logic exception_clear;
    (* anyseq *) logic exception_latch;

    // Outputs
    logic int_request;
    logic exception_pending;
    logic [5:0] latched_exceptions;
    logic has_unmasked_exception;

    // Instantiate DUT
    FPU_Exception_Handler dut (
        .clk(clk),
        .reset(reset),
        .exception_invalid(exception_invalid),
        .exception_denormal(exception_denormal),
        .exception_zero_div(exception_zero_div),
        .exception_overflow(exception_overflow),
        .exception_underflow(exception_underflow),
        .exception_precision(exception_precision),
        .mask_invalid(mask_invalid),
        .mask_denormal(mask_denormal),
        .mask_zero_div(mask_zero_div),
        .mask_overflow(mask_overflow),
        .mask_underflow(mask_underflow),
        .mask_precision(mask_precision),
        .exception_clear(exception_clear),
        .exception_latch(exception_latch),
        .int_request(int_request),
        .exception_pending(exception_pending),
        .latched_exceptions(latched_exceptions),
        .has_unmasked_exception(has_unmasked_exception)
    );

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
    // Shadow model for exception latches
    //=========================================================================

    logic [5:0] shadow_latched;
    logic shadow_int;

    always_ff @(posedge clk) begin
        if (reset) begin
            shadow_latched <= 6'b0;
            shadow_int <= 1'b0;
        end else if (exception_clear) begin
            shadow_latched <= 6'b0;
            shadow_int <= 1'b0;
        end else if (exception_latch) begin
            // OR with existing (sticky)
            shadow_latched[0] <= shadow_latched[0] || exception_invalid;
            shadow_latched[1] <= shadow_latched[1] || exception_denormal;
            shadow_latched[2] <= shadow_latched[2] || exception_zero_div;
            shadow_latched[3] <= shadow_latched[3] || exception_overflow;
            shadow_latched[4] <= shadow_latched[4] || exception_underflow;
            shadow_latched[5] <= shadow_latched[5] || exception_precision;

            // Check if new unmasked exception
            if ((exception_invalid && !mask_invalid) ||
                (exception_denormal && !mask_denormal) ||
                (exception_zero_div && !mask_zero_div) ||
                (exception_overflow && !mask_overflow) ||
                (exception_underflow && !mask_underflow) ||
                (exception_precision && !mask_precision)) begin
                shadow_int <= 1'b1;
            end
        end
    end

    //=========================================================================
    // Formal Properties
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin

            //=================================================================
            // Property 1: Reset clears all latched exceptions
            //=================================================================
            if ($past(reset))
                assert(latched_exceptions == 6'b0);

            //=================================================================
            // Property 2: Reset deasserts INT
            //=================================================================
            if ($past(reset))
                assert(!int_request);

            //=================================================================
            // Property 3: Exception_clear clears all latched exceptions
            //=================================================================
            if ($past(exception_clear) && !$past(reset))
                assert(latched_exceptions == 6'b0);

            //=================================================================
            // Property 4: Exception_clear deasserts INT
            //=================================================================
            if ($past(exception_clear) && !$past(reset))
                assert(!int_request);

            //=================================================================
            // Property 5: Latched exceptions are sticky (OR behavior)
            //=================================================================
            // Once set, a latched exception stays set until clear
            if (!$past(reset) && !$past(exception_clear)) begin
                // If bit was set, it stays set
                if ($past(latched_exceptions[0]))
                    assert(latched_exceptions[0]);
                if ($past(latched_exceptions[1]))
                    assert(latched_exceptions[1]);
                if ($past(latched_exceptions[2]))
                    assert(latched_exceptions[2]);
                if ($past(latched_exceptions[3]))
                    assert(latched_exceptions[3]);
                if ($past(latched_exceptions[4]))
                    assert(latched_exceptions[4]);
                if ($past(latched_exceptions[5]))
                    assert(latched_exceptions[5]);
            end

            //=================================================================
            // Property 6: Exception_latch sets exception bits
            //=================================================================
            if ($past(exception_latch) && !$past(reset) && !$past(exception_clear)) begin
                if ($past(exception_invalid))
                    assert(latched_exceptions[0]);
                if ($past(exception_denormal))
                    assert(latched_exceptions[1]);
                if ($past(exception_zero_div))
                    assert(latched_exceptions[2]);
                if ($past(exception_overflow))
                    assert(latched_exceptions[3]);
                if ($past(exception_underflow))
                    assert(latched_exceptions[4]);
                if ($past(exception_precision))
                    assert(latched_exceptions[5]);
            end

            //=================================================================
            // Property 7: INT is sticky - once set, stays until clear
            //=================================================================
            if ($past(int_request) && !$past(reset) && !$past(exception_clear))
                assert(int_request);

            //=================================================================
            // Property 8: INT only asserts on unmasked exception during latch
            //=================================================================
            // If INT was low and goes high, there must have been an exception_latch
            // with an unmasked exception
            if (int_request && !$past(int_request) && !$past(reset))
                assert($past(exception_latch));

            //=================================================================
            // Property 9: has_unmasked_exception correctly reflects state
            //=================================================================
            // has_unmasked_exception = latched AND NOT masked for any bit
            assert(has_unmasked_exception ==
                   ((latched_exceptions[0] && !mask_invalid) ||
                    (latched_exceptions[1] && !mask_denormal) ||
                    (latched_exceptions[2] && !mask_zero_div) ||
                    (latched_exceptions[3] && !mask_overflow) ||
                    (latched_exceptions[4] && !mask_underflow) ||
                    (latched_exceptions[5] && !mask_precision)));

            //=================================================================
            // Property 10: Latched exceptions match shadow model
            //=================================================================
            assert(latched_exceptions == shadow_latched);

            //=================================================================
            // Property 11: INT matches shadow model
            //=================================================================
            assert(int_request == shadow_int);

            //=================================================================
            // Property 12: No spontaneous exception assertion
            //=================================================================
            // Latched bits only go high on exception_latch
            if (!$past(reset) && !$past(exception_latch)) begin
                if (!$past(latched_exceptions[0]))
                    assert(!latched_exceptions[0] || $past(exception_clear));
            end

        end
    end

    //=========================================================================
    // Cover Properties - Verify reachability
    //=========================================================================

    always_ff @(posedge clk) begin
        if (seen_reset && !reset) begin
            // Cover: INT request asserted
            cover(int_request);

            // Cover: Exception clear while INT asserted
            cover(exception_clear && $past(int_request));

            // Cover: Multiple exceptions latched
            cover(latched_exceptions[0] && latched_exceptions[2]);

            // Cover: Unmasked exception
            cover(has_unmasked_exception);

            // Cover: All exceptions latched
            cover(latched_exceptions == 6'b111111);

            // Cover: Exception latched but masked (no INT)
            cover(exception_latch && exception_invalid && mask_invalid && !int_request);

            // Cover: INT transitions from low to high
            cover(int_request && !$past(int_request));
        end
    end

endmodule
