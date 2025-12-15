// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// Payne-Hanek Extended Precision Constants ROM
//
// Stores high-precision representations of mathematical constants:
// - 2/π (256 bits in 4 × 64-bit chunks)
// - π/2 (80 bits, single constant)
//
// Used by microcode for extended precision range reduction.
//
// ROM Address Map:
//   0: TWO_OVER_PI_CHUNK0 (bits 255:192) - raw bits
//   1: TWO_OVER_PI_CHUNK1 (bits 191:128) - raw bits
//   2: TWO_OVER_PI_CHUNK2 (bits 127:64) - raw bits
//   3: TWO_OVER_PI_CHUNK3 (bits 63:0) - raw bits
//   4: PI_OVER_2 (80-bit FP80)
//   5: TWO_OVER_PI_FP80 (80-bit FP80) - Phase 3
//
// Area: ~45-55 LUTs (~6-8 ALMs on Cyclone V)
// Latency: 1 cycle (registered output)
//=====================================================================

module FPU_Payne_Hanek_ROM(
    input wire clk,
    input wire [2:0] addr,  // Address: 0-4
    output reg [79:0] data_out
);

    //=================================================================
    // Extended Precision 2/π Representation (256 bits)
    //
    // 2/π = 0.636619772367581343075535053490057448...
    //
    // Hexadecimal (first 256 bits):
    // 0xA2F9836E4E441529FC2757D1F534DDC0DB629599BD80F66B7A1D01FE7C46E5E2
    //
    // Split into 4 × 64-bit chunks for multi-precision multiplication:
    //=================================================================

    localparam [63:0] TWO_OVER_PI_CHUNK0 = 64'hA2F9836E4E441529; // bits 255:192
    localparam [63:0] TWO_OVER_PI_CHUNK1 = 64'hFC2757D1F534DDC0; // bits 191:128
    localparam [63:0] TWO_OVER_PI_CHUNK2 = 64'hDB629599BD80F66B; // bits 127:64
    localparam [63:0] TWO_OVER_PI_CHUNK3 = 64'h7A1D01FE7C46E5E2; // bits 63:0

    //=================================================================
    // π/2 Constant (80-bit IEEE 754 Extended Precision)
    //
    // π/2 = 1.5707963267948966...
    // FP80: sign=0, exponent=0x3FFF, mantissa=0xC90FDAA22168C235
    //=================================================================

    localparam [79:0] PI_OVER_2 = 80'h3FFF_C90FDAA22168C235;

    //=================================================================
    // 2/π as FP80 Constant (80-bit IEEE 754 Extended Precision)
    //
    // 2/π = 0.6366197723675814...
    // = 1.2732395447351627... × 2^(-1)
    // FP80: sign=0, exponent=0x3FFE, mantissa=0xA2F9836E4E441529
    //=================================================================

    localparam [79:0] TWO_OVER_PI_FP80 = 80'h3FFE_A2F9836E4E441529;

    //=================================================================
    // ROM Logic - Registered Output
    //=================================================================

    always @(posedge clk) begin
        case (addr)
            3'd0: data_out <= {16'd0, TWO_OVER_PI_CHUNK0}; // Zero-extend to 80 bits
            3'd1: data_out <= {16'd0, TWO_OVER_PI_CHUNK1};
            3'd2: data_out <= {16'd0, TWO_OVER_PI_CHUNK2};
            3'd3: data_out <= {16'd0, TWO_OVER_PI_CHUNK3};
            3'd4: data_out <= PI_OVER_2;
            3'd5: data_out <= TWO_OVER_PI_FP80;  // Phase 3: 2/π as FP80
            default: data_out <= 80'd0;
        endcase
    end

endmodule
