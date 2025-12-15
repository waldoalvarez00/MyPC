// Multi-bit Bus Synchronizer
// Synchronizes a multi-bit value across clock domains
//
// Copyright 2024
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

`default_nettype none

module BusSync #(
    parameter WIDTH = 8
)(
    input logic clk,
    input logic reset,
    input logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);

// Use generic synchronizer for simulation, Altera primitive for synthesis
`ifdef verilator
    `define USE_GENERIC_SYNC
`elsif ICARUS
    `define USE_GENERIC_SYNC
`elsif SIMULATION
    `define USE_GENERIC_SYNC
`endif

`ifdef USE_GENERIC_SYNC

// Generic 2-stage synchronizer for simulation
// Each bit is synchronized independently
reg [WIDTH-1:0] p1;
reg [WIDTH-1:0] p2;

assign q = p2;

always_ff @(posedge clk or posedge reset) begin
    if (reset)
        p1 <= {WIDTH{1'b0}};
    else
        p1 <= d;
end

always_ff @(posedge clk or posedge reset) begin
    if (reset)
        p2 <= {WIDTH{1'b0}};
    else
        p2 <= p1;
end

`else

// Altera-specific synchronizer for FPGA synthesis
// Instantiate WIDTH separate synchronizers
genvar i;
generate
    for (i = 0; i < WIDTH; i = i + 1) begin : sync_gen
        altera_std_synchronizer sync_bit (
            .clk(clk),
            .reset_n(~reset),
            .din(d[i]),
            .dout(q[i])
        );
    end
endgenerate

`endif

`ifdef USE_GENERIC_SYNC
    `undef USE_GENERIC_SYNC
`endif

endmodule
