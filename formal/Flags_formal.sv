// Formal harness for Quartus/rtl/CPU/Flags.sv

`default_nettype none

module Flags_formal(
    input clk
);
    // Clock and reset
    reg reset;

    // Inputs
    (* anyseq *) reg [15:0] flags_in;
    (* anyseq *) reg [8:0]  update_flags;

    // Output
    wire [15:0] flags_out;

    // DUT
    Flags dut (
        .clk(clk),
        .reset(reset),
        .flags_in(flags_in),
        .update_flags(update_flags),
        .flags_out(flags_out)
    );

    // Basic reset: start in reset, then release
    initial reset = 1'b1;

    reg seen_reset;

    always @(posedge clk) begin
        if ($initstate) begin
            reset      <= 1'b1;
            seen_reset <= 1'b0;
        end else begin
            reset      <= 1'b0;
            if (reset)
                seen_reset <= 1'b1;
        end
    end

    // Safety properties
    always @(posedge clk) if (seen_reset && !reset) begin
        // On the cycle after reset, Flags must come up in the expected reset state.
        if ($past(reset))
            assert(flags_out == 16'h0002);

        // Architectural invariant bits: high nibble and reserved bits.
        assert(flags_out[15:12] == 4'b0000);
        assert(flags_out[5]     == 1'b0);
        assert(flags_out[3]     == 1'b0);
        assert(flags_out[1]     == 1'b1);
    end

endmodule

