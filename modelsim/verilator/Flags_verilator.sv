// ================================================================
// Flags Module for Verilator (with built-in constant definitions)
// This is a copy of Flags.sv with constants defined inline
// ================================================================

`default_nettype none

module Flags_verilator(
    input logic clk,
    input logic reset,
    input logic [15:0] flags_in,
    input logic [8:0] update_flags,
    output logic [15:0] flags_out
);

// Flag indices in 16-bit register
localparam CF_IDX = 4'd0;
localparam PF_IDX = 4'd2;
localparam AF_IDX = 4'd4;
localparam ZF_IDX = 4'd6;
localparam SF_IDX = 4'd7;
localparam TF_IDX = 4'd8;
localparam IF_IDX = 4'd9;
localparam DF_IDX = 4'd10;
localparam OF_IDX = 4'd11;

// Update flags bit positions
localparam UpdateFlags_CF = 4'd0;
localparam UpdateFlags_PF = 4'd1;
localparam UpdateFlags_AF = 4'd2;
localparam UpdateFlags_ZF = 4'd3;
localparam UpdateFlags_SF = 4'd4;
localparam UpdateFlags_TF = 4'd5;
localparam UpdateFlags_IF = 4'd6;
localparam UpdateFlags_DF = 4'd7;
localparam UpdateFlags_OF = 4'd8;

// Internal flag registers
reg C, P, A, Z, S, T, I, D, O;

// Output assignment: {4'b0000, O, D, I, T, S, Z, 1'b0, A, 1'b0, P, 1'b1, C}
assign flags_out = {4'b0000, O, D, I, T, S, Z, 1'b0, A, 1'b0, P, 1'b1, C};

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        C <= 1'b0;
        P <= 1'b0;
        A <= 1'b0;
        Z <= 1'b0;
        S <= 1'b0;
        T <= 1'b0;
        I <= 1'b0;
        D <= 1'b0;
        O <= 1'b0;
    end else begin
        C <= update_flags[UpdateFlags_CF] ? flags_in[CF_IDX] : C;
        P <= update_flags[UpdateFlags_PF] ? flags_in[PF_IDX] : P;
        A <= update_flags[UpdateFlags_AF] ? flags_in[AF_IDX] : A;
        Z <= update_flags[UpdateFlags_ZF] ? flags_in[ZF_IDX] : Z;
        S <= update_flags[UpdateFlags_SF] ? flags_in[SF_IDX] : S;
        T <= update_flags[UpdateFlags_TF] ? flags_in[TF_IDX] : T;
        I <= update_flags[UpdateFlags_IF] ? flags_in[IF_IDX] : I;
        D <= update_flags[UpdateFlags_DF] ? flags_in[DF_IDX] : D;
        O <= update_flags[UpdateFlags_OF] ? flags_in[OF_IDX] : O;
    end
end

endmodule
