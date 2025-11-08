
module FPU_Stack_Registers;

// Define 8 80-bit wide floating-point registers
reg [79:0] ST[7:0]; 

// Aliases for extended-precision real format
wire [0:0] sign_extended[7:0];
wire [14:0] exponent_extended[7:0];
wire [63:0] fraction_extended[7:0];

// Aliases for double-precision real format
wire [0:0] sign_double[7:0];
wire [10:0] exponent_double[7:0];
wire [51:0] fraction_double[7:0];

// Aliases for single-precision real format
wire [0:0] sign_single[7:0];
wire [7:0] exponent_single[7:0];
wire [22:0] fraction_single[7:0];


// Aliases for integer formats
wire [63:0] binary_integer_64 [7:0]; // 64-bit binary integer
wire [31:0] binary_integer_32 [7:0]; // 32-bit binary integer
wire [15:0] binary_integer_16 [7:0]; // 16-bit binary integer

// Alias for BCD format (18-digit)
wire [71:0] bcd_18_digit [7:0]; // 18-digit BCD (using 72 bits)


// Generate aliases for each format
genvar i;
generate
    for (i = 0; i < 8; i = i + 1) begin: generate_aliases
        assign sign_extended[i] = ST[i][79];
        assign exponent_extended[i] = ST[i][78:64];
        assign fraction_extended[i] = ST[i][63:0];

        assign sign_double[i] = ST[i][79];
        assign exponent_double[i] = ST[i][78:68];
        assign fraction_double[i] = ST[i][67:16];

        assign sign_single[i] = ST[i][79];
        assign exponent_single[i] = ST[i][78:71];
        assign fraction_single[i] = ST[i][70:48];

        assign binary_integer_64[i] = ST[i][63:0];
        assign binary_integer_32[i] = ST[i][31:0];
        assign binary_integer_16[i] = ST[i][15:0];
        assign bcd_18_digit[i] = ST[i][71:0]; // Assuming lower 72 bits are used for BCD
    end
endgenerate

endmodule