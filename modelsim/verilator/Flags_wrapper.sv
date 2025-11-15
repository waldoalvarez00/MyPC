// ================================================================
// Wrapper for Flags module with constant definitions
// Provides flag indices and update flag constants
// ================================================================

`default_nettype none

// Include flag definitions
`include "FlagsDefinitions.svh"

module Flags_wrapper(
    input logic clk,
    input logic reset,
    input logic [15:0] flags_in,
    input logic [8:0] update_flags,
    output logic [15:0] flags_out
);

// Instantiate the actual Flags module
Flags flags_inst (
    .clk(clk),
    .reset(reset),
    .flags_in(flags_in),
    .update_flags(update_flags),
    .flags_out(flags_out)
);

endmodule
