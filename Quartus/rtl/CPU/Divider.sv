// Copyright Jamie Iles, 2017
//
// This file is part of s80x86.
//
// s80x86 is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// s80x86 is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with s80x86.  If not, see <http://www.gnu.org/licenses/>.



// Non-restoring division

// Newton Raphson?


/*


module div_nonrestoring (a,b,start,clk,clrn,q,r,busy,ready,count);

input [31:0] a; // dividend
input [15:0] b; // divisor
input start; // start
input clk, clrn; // clk,reset
output [31:0] q; // quotient
output [15:0] r; // remainder
output reg busy; // busy
output reg ready; // ready
output [4:0] count; // count

reg [31:0] reg_q;
reg [15:0] reg_r;
reg [15:0] reg_b;
reg [4:0] count;

wire [16:0] sub_add = reg_r[15]? {reg_r,reg_q[31]} + {1’b0,reg_b} : // + b
                                 {reg_r,reg_q[31]} - {1’b0,reg_b}; // - b

assign q = reg_q;
assign r = reg_r[15]? reg_r + reg_b : reg_r; // adjust r

always @ (posedge clk or negedge clrn) begin
  if (!clrn) begin
  busy <= 0;
  ready <= 0;
  end else begin
  if (start) begin
  reg_q <= a; // load a
  reg_b <= b; // load b
  reg_r <= 0;
  busy <= 1;
  ready <= 0;
  count <= 0;
  end else if (busy) begin
   reg_q <= {reg_q[30:0],̃sub_add[16]}; // << 1
   reg_r <= sub_add[15:0];
   count <= count + 5’b1; // count++
   if (count == 5’h1f) begin // finish
   busy <= 0;
   ready <= 1; // q,r ready
  end
end
end
end
endmodule






module Divider_nonrestoring(
    input logic clk,
    input logic reset,
    input logic start,
    input logic is_8_bit,
    input logic is_signed,
    output logic busy,
    output logic complete,
    output logic error,
    input logic [31:0] dividend,
    input logic [15:0] divisor,
    output logic [15:0] quotient,
    output logic [15:0] remainder
);

reg [31:0] reg_q;
reg [31:0] reg_r; // Extended to 32 bits to handle sign extension for signed division
reg [31:0] reg_b; // Extended to 32 bits for alignment and signed operations
reg [4:0] count;
wire [32:0] sub_add; // Extended for potential carry or borrow

// Adjusting the operation based on signed or unsigned mode
assign sub_add = reg_r[31] ? {reg_r, reg_q[31]} + {1'b0, reg_b} : {reg_r, reg_q[31]} - {1'b0, reg_b};

// Assign outputs, adjusting the remainder for signed division if necessary
assign quotient = reg_q[31:16]; // Adjusted to provide the correct quotient part
assign remainder = reg_r[15:0]; // Taking only the lower 16 bits as the remainder

always @(posedge clk or negedge reset) begin
    if (!reset) begin
        busy <= 0;
        complete <= 0;
        reg_q <= 0;
        reg_r <= 0;
        count <= 0;
        error <= 0;
    end else if (start) begin
        reg_q <= dividend; // Loading the dividend
        reg_b <= is_8_bit ? {16'b0, divisor[7:0]} : {16'b0, divisor}; // Extending divisor based on mode
        reg_r <= 0;
        busy <= 1;
        complete <= 0;
        count <= 0;
        error <= (divisor == 0); // Error if divisor is zero
    end else if (busy) begin
        reg_q <= {reg_q[30:0], ~sub_add[32]}; // Shift left and update sign
        reg_r <= sub_add[31:0]; // Update remainder
        count <= count + 1;
        if (count == 5'h1F) begin // Finish condition
            busy <= 0;
            complete <= 1; // Indicate completion
            if (is_signed && dividend[31]) begin
                // Adjusting the quotient and remainder for negative dividends in signed mode
                quotient <= -reg_q[31:16];
                remainder <= -reg_r[15:0];
            end
        end
    end
end

endmodule







module goldschmidt (a,b,start,clk,clrn,q,busy,ready,count,yn);
input [31:0] a; // dividend: .1xxx...x
input [31:0] b; // divisor: .1xxx...x
input start; // start
input clk, clrn; // clock and reset
output [31:0] q; // quotient: x.xxx...x
output reg busy; // busy

output reg ready; // ready
output [2:0] count; // counter
output [31:0] yn; // .11111...1
reg [63:0] reg_a; // x.xxxx...x
reg [63:0] reg_b; // 0.xxxx...x
reg [2:0] count;
wire [63:0] two_minus_yi = ̃reg_b + 1’b1; // 1.xxxx...x (2 - yi)
wire [127:0] xi = reg_a * two_minus_yi; // 0x.xxx...x
wire [127:0] yi = reg_b * two_minus_yi; // 0x.xxx...x
assign q = reg_a[63:32] + |reg_a[31:29]; // rounding up
assign yn = reg_b[62:31];
always @ (posedge clk or negedge clrn) begin
if (!clrn) begin
busy <= 0;
ready <= 0;
end else begin
if (start) begin
reg_a <= {1’b0,a,31’b0}; // 0.1x...x0...0
reg_b <= {1’b0,b,31’b0}; // 0.1x...x0...0
busy <= 1;
ready <= 0;
count <= 0;
end else begin
reg_a <= xi[126:63]; // x.xxx...x
reg_b <= yi[126:63]; // 0.xxx...x
count <= count + 3’b1; // count++
if (count == 3’h4) begin // finish
busy <= 0;
ready <= 1; // q is ready
end
end
end
end
endmodule


module Divider_goldschmidt(
    input logic clk,
    input logic reset,
    input logic start,
    input logic is_8_bit,
    input logic is_signed,
    output logic busy,
    output logic complete,
    output logic error,
    input logic [31:0] dividend,
    input logic [15:0] divisor,
    output logic [15:0] quotient,
    output logic [15:0] remainder
);

reg [63:0] reg_a, reg_b; // Extended registers for division operation
reg [31:0] a, b; // Adjusted dividend and divisor based on mode
wire [63:0] two_minus_yi;
wire [127:0] xi, yi;
reg [2:0] count;
assign two_minus_yi = ~reg_b + 1'b1;
assign xi = reg_a * two_minus_yi;
assign yi = reg_b * two_minus_yi;

// Outputs
assign quotient = reg_a[63:48] + |reg_a[47:46]; // Rounding up for quotient
assign remainder = reg_a[47:32]; // Capturing remainder
assign complete = (count == 3'h4); // Indicate completion after certain cycles
assign error = (divisor == 0); // Error if divisor is zero

always @(posedge clk or negedge reset) begin
    if (!reset) begin
        busy <= 0;
        complete <= 0;
        count <= 0;
        error <= 0;
    end else if (start) begin
        // Adjust inputs based on is_8_bit and is_signed flags
        if (is_8_bit) begin
            a = is_signed ? {24'b0, dividend[7:0]} : {24'b0, dividend[7:0]};
            b = is_signed ? {48'b0, divisor[7:0]} : {48'b0, divisor[7:0]};
        end else begin
            a = is_signed ? {16'b0, dividend[15:0]} : {16'b0, dividend[15:0]};
            b = is_signed ? {48'b0, divisor[15:0]} : {48'b0, divisor[15:0]};
        end
        reg_a <= {1'b0, a, 31'b0}; // Adjusted based on input size
        reg_b <= {1'b0, b, 31'b0};
        busy <= 1;
        complete <= 0;
        count <= 0;
        error <= (divisor == 0);
    end else if (busy) begin
        reg_a <= xi[126:63]; // Update reg_a with the new approximation
        reg_b <= yi[126:63]; // Update reg_b with the new approximation
        count <= count + 3'b1; // Increment counter
        if (count == 3'h4) begin
            busy <= 0;
            complete <= 1; // Indicate division complete
        end
    end
end

endmodule


*/

`default_nettype none
module Divider(input logic clk,
               input logic reset,
               input logic start,
               input logic is_8_bit,
               input logic is_signed,
               output logic busy,
               output logic complete,
               output logic error,
               input logic [31:0] dividend,
               input logic [15:0] divisor,
               output logic [15:0] quotient,
               output logic [15:0] remainder);

typedef enum bit[1:0] {
    INIT,
    WORKING,
    RESTORE,
    FIX_SIGN
} DivState_t;

DivState_t state, next_state;

// Remainder
wire [15:0] rem8 = {{8{P[15]}}, P[15:8]};
wire [15:0] rem16 = P[31:16];
assign remainder = is_8_bit ? rem8 : rem16;

// Shifted divisor
wire [31:0] udivshift8 = {16'b0, divisor[7:0], 8'b0};
wire [31:0] udivshift16 = {divisor, 16'b0};
wire [31:0] udivshift = is_8_bit ? udivshift8 : udivshift16;

wire [31:0] sdivshift8 = {16'b0, divisor_mag[7:0], 8'b0};
wire [31:0] sdivshift16 = {divisor_mag, 16'b0};
wire [31:0] sdivshift = is_8_bit ? sdivshift8 : sdivshift16;

wire [31:0] D = is_signed ? sdivshift : udivshift;

// Overflow
wire unsigned_overflow8 = dividend[15:0] >= {divisor[7:0], 8'b0};
wire unsigned_overflow16 = dividend >= {divisor, 16'b0};
wire unsigned_overflow = is_8_bit ? unsigned_overflow8 : unsigned_overflow16;

wire signed_overflow8 = in_signs_equal && dividend_mag[14:7] >= divisor_mag[7:0];
wire signed_overflow16 = in_signs_equal && dividend_mag[30:15] >= divisor_mag;
wire signed_overflow = is_8_bit ? signed_overflow8 : signed_overflow16;

wire overflow = is_signed ? signed_overflow : unsigned_overflow;
wire div_by_zero = divisor == 16'b0;

// Magnitudes
wire [31:0] dividend_mag = (dividend + {32{dividend[31]}}) ^ {32{dividend[31]}};
wire [15:0] divisor_mag = (divisor + {16{divisor[15]}}) ^ {16{divisor[15]}};

// Dividend
wire [63:0] P16 = is_signed ?
    {32'b0, dividend_mag} : {32'b0, dividend};
wire [63:0] P8 = is_signed ?
    {48'b0, dividend_mag[15:0]} : {48'b0, dividend[15:0]};
wire [63:0] P_init = is_8_bit ? P8 : P16;

// Sign bits
wire in_signs_equal8 = ~(dividend[15] ^ divisor[7]);
wire in_signs_equal16 = ~(dividend[31] ^ divisor[15]);
wire in_signs_equal = is_8_bit ? in_signs_equal8 : in_signs_equal16;
wire dividend_negative = is_8_bit ? dividend[15] : dividend[31];

reg [63:0] P;
reg [3:0] idx;
reg [15:0] restored_quotient;
wire [15:0] negative_quotient = ~quotient + 1'b1;

// Extract P sign bit to avoid Icarus Verilog constant select issue
wire p_sign = P[63];

// Error condition
wire raise_error = div_by_zero | overflow;

assign busy = start || ((state != INIT) && !complete);

always_comb begin
    if (is_8_bit) begin
        restored_quotient = {8'b0, p_sign ?
            quotient[7:0] - ~quotient[7:0] - 8'b1 : quotient[7:0] - ~quotient[7:0]};
    end else begin
        restored_quotient = p_sign ?
            quotient - ~quotient - 16'b1 : quotient - ~quotient;
    end
end




always_comb begin
    case (state)
    INIT: next_state = DivState_t'(start && !error && !raise_error ? WORKING : INIT);
    WORKING: next_state = DivState_t'(idx == 4'b0 ? RESTORE : WORKING);
    RESTORE: next_state = DivState_t'(is_signed ? FIX_SIGN : INIT);
    FIX_SIGN: next_state = INIT;
    endcase

    if (reset)
        next_state = INIT;
end




always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        error <= 1'b0;
        complete <= 1'b0;
    end else begin
        case (state)
        INIT: begin
            error <= 1'b0;

            if (start) begin
                quotient <= 16'b0;
                P <= P_init;
                idx <= !is_8_bit ? 4'hf : 4'h7;
                error <= raise_error;
            end

            complete <= start && raise_error;
        end
        WORKING: begin
            if (!p_sign) begin
                quotient[idx] <= 1'b1;
                P <= (P * 2) - {32'b0, D};
            end else begin
                P <= (P * 2) + {32'b0, D};
            end
            idx <= idx - 1'b1;
        end
        RESTORE: begin
            quotient <= restored_quotient;
            if (p_sign)
                P <= P + {{32{D[31]}}, D};
            complete <= ~is_signed;
        end
        FIX_SIGN: begin
            if (~in_signs_equal) begin
                quotient <= negative_quotient;
                error <= |quotient & is_signed & ~negative_quotient[is_8_bit ? 7 : 15];
            end else begin
                error <= |quotient & is_signed & quotient[is_8_bit ? 7 : 15];
            end
            if (dividend_negative && is_8_bit)
                P[15:8] <= ~P[15:8] + 1'b1;
            else if (dividend_negative)
                P[31:16] <= ~P[31:16] + 1'b1;
            complete <= 1'b1;
        end
        endcase
    end
end

always_ff @(posedge clk or posedge reset) begin
    if (reset)
        state <= INIT;
    else
        state <= next_state;
end

endmodule
