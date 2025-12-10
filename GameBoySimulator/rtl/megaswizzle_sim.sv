//
// Megaswizzle Simulation Stub
// Passes through all signals without swizzling
//

module megaduck_swizzle (
    input         megaduck,
    input  [15:0] a_in,      // 16-bit address bus!
    input  [7:0]  snd_in_di,
    input  [7:0]  snd_out_di,
    output [15:0] a_out,     // 16-bit address bus!
    output [7:0]  snd_in_do,
    output [7:0]  snd_out_do,
    input  [7:0]  d_in,
    output [7:0]  d_out
);

    // Pass through without modification (megaduck mode not supported in sim)
    assign a_out = a_in;
    assign snd_in_do = snd_in_di;
    assign snd_out_do = snd_out_di;
    assign d_out = d_in;

endmodule
