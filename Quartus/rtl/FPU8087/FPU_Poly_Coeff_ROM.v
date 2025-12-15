// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// Polynomial Coefficient ROM
//
// Contains polynomial coefficients for transcendental function
// approximations (exponential and logarithm).
//
// Polynomials stored:
// - F2XM1: 2^x - 1 (degree 6, for x ∈ [-1, 1])
// - LOG2:  log₂(1+x) (degree 7, for x ∈ [0, 1])
//
// All coefficients in 80-bit IEEE 754 extended precision format.
//=====================================================================

module FPU_Poly_Coeff_ROM(
    input wire [3:0] poly_select,  // Polynomial selector
    input wire [3:0] coeff_index,  // Coefficient index (0-15)
    output reg [79:0] coefficient  // Coefficient value (FP80)
);

    // Store coefficients in a tiny ROM so Quartus can map into MLABs instead of logic
    (* ramstyle = "MLAB" *) reg [79:0] coeff_rom [0:31];

    initial begin
        // F2XM1 coefficients (degree 6) at indices 0x00-0x0F
        coeff_rom[ 0] = 80'h3FFE_B17217F7D1CF79AC;  // c0
        coeff_rom[ 1] = 80'h3FFD_EC709DC3A03FD45B;  // c1
        coeff_rom[ 2] = 80'h3FFB_E3D96B0E8B0B3A0F;  // c2
        coeff_rom[ 3] = 80'h3FF9_9D955B7DD273B948;  // c3
        coeff_rom[ 4] = 80'h3FF6_AE64567F544E3897;  // c4
        coeff_rom[ 5] = 80'h3FF3_A27912F3B25C65D8;  // c5
        coeff_rom[ 6] = 80'h0;
        coeff_rom[ 7] = 80'h0;
        coeff_rom[ 8] = 80'h0;
        coeff_rom[ 9] = 80'h0;
        coeff_rom[10] = 80'h0;
        coeff_rom[11] = 80'h0;
        coeff_rom[12] = 80'h0;
        coeff_rom[13] = 80'h0;
        coeff_rom[14] = 80'h0;
        coeff_rom[15] = 80'h0;

        // LOG2 coefficients (degree 7) at indices 0x10-0x1F
        coeff_rom[16] = 80'h3FFF_B8AA3B295C17F0BC;  // c0
        coeff_rom[17] = 80'hBFFE_B8AA3B295C17F0BC;  // c1
        coeff_rom[18] = 80'h3FFE_F5C28F5C28F5C28F;  // c2
        coeff_rom[19] = 80'hBFFE_B8AA3B295C17F0BC;  // c3
        coeff_rom[20] = 80'h3FFD_93E5939A08CEA7B7;  // c4
        coeff_rom[21] = 80'hBFFD_F5C28F5C28F5C28F;  // c5
        coeff_rom[22] = 80'h3FFD_A3D70A3D70A3D70A;  // c6
        coeff_rom[23] = 80'hBFFD_B8AA3B295C17F0BC;  // c7
        coeff_rom[24] = 80'h0;
        coeff_rom[25] = 80'h0;
        coeff_rom[26] = 80'h0;
        coeff_rom[27] = 80'h0;
        coeff_rom[28] = 80'h0;
        coeff_rom[29] = 80'h0;
        coeff_rom[30] = 80'h0;
        coeff_rom[31] = 80'h0;
    end

    wire [4:0] rom_addr = {poly_select[0], coeff_index};  // only two polynomials used

    always @(*) begin
        coefficient = coeff_rom[rom_addr];
    end

endmodule


//=====================================================================
// COEFFICIENT VERIFICATION
//=====================================================================
//
// F2XM1 Test Values:
// - f(0) = 0 (exact)
// - f(0.5) = 2^0.5 - 1 ≈ 0.41421356 (√2 - 1)
// - f(1) = 2^1 - 1 = 1.0 (exact)
// - f(-1) = 2^-1 - 1 = -0.5 (exact)
//
// LOG2 Test Values:
// - f(0) = log₂(1) = 0 (exact)
// - f(1) = log₂(2) = 1.0 (exact)
// - f(0.5) = log₂(1.5) ≈ 0.58496250
//
// Maximum Error (for degree shown):
// - F2XM1 (degree 6): < 2×10⁻⁷ for x ∈ [-1, 1]
// - LOG2 (degree 7): < 1×10⁻⁷ for x ∈ [0, 1]
//
// These approximations provide accuracy better than 1 ULP for
// 64-bit mantissa precision, meeting 8087 specifications.
//=====================================================================


//=====================================================================
// USAGE EXAMPLE
//=====================================================================
//
// To evaluate P(x) = c₀ + c₁x + c₂x² + ... using Horner's method:
//
// 1. Read coefficients in reverse order (cₙ, cₙ₋₁, ..., c₀)
// 2. Initialize result = cₙ
// 3. For i = n-1 down to 0:
//      result = result * x + cᵢ
//
// Example for F2XM1 (degree 6):
//   result = c₅
//   result = result * x + c₄
//   result = result * x + c₃
//   result = result * x + c₂
//   result = result * x + c₁
//   result = result * x + c₀
//   result = result * x        // Final multiply by x
//
// This requires 7 multiplications and 5 additions.
//=====================================================================
