// ================================================================
// Flag Definitions for Verilator Testbench
// Defines flag indices and update flag bit positions as constants
// ================================================================

`ifndef FLAGS_DEFINITIONS_SVH
`define FLAGS_DEFINITIONS_SVH

// Flag indices in 16-bit flags register
`define CF_IDX 4'd0
`define PF_IDX 4'd2
`define AF_IDX 4'd4
`define ZF_IDX 4'd6
`define SF_IDX 4'd7
`define TF_IDX 4'd8
`define IF_IDX 4'd9
`define DF_IDX 4'd10
`define OF_IDX 4'd11

// Update flags bit positions (9-bit mask)
`define UpdateFlags_CF 4'd0
`define UpdateFlags_PF 4'd1
`define UpdateFlags_AF 4'd2
`define UpdateFlags_ZF 4'd3
`define UpdateFlags_SF 4'd4
`define UpdateFlags_TF 4'd5
`define UpdateFlags_IF 4'd6
`define UpdateFlags_DF 4'd7
`define UpdateFlags_OF 4'd8

`endif // FLAGS_DEFINITIONS_SVH
