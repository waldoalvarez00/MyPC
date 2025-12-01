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

`default_nettype none
module RegisterFile(input logic clk,
                    input logic reset,
                    input logic is_8_bit,
                    output logic [15:0] si,
                    output logic [15:0] di,
                    output logic [15:0] bp,
                    output logic [15:0] bx,
                    // Read port.
                    input logic [2:0] rd_sel[2],
                    output logic [15:0] rd_val[2],
                    // Write port.
                    input logic [2:0] wr_sel,
                    input logic [15:0] wr_val,
                    input logic wr_en);

reg [15:0] gprs[8];

wire wr_sel_low_byte = ~wr_sel[2];
wire [2:0] wr_8_bit_sel = {1'b0, wr_sel[1:0]};

// Initialize registers on reset for simulation
integer i;
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        for (i = 0; i < 8; i = i + 1)
            gprs[i] <= 16'h0000;
    end else if (wr_en) begin
        if (is_8_bit) begin
            if (wr_sel_low_byte)
                gprs[wr_8_bit_sel][7:0] <= wr_val[7:0];
            else
                gprs[wr_8_bit_sel][15:8] <= wr_val[7:0];
        end else begin
            gprs[wr_sel] <= wr_val;
        end
    end
end

always_ff @(posedge clk) begin
    si <= wr_en && !is_8_bit && wr_sel == SI ? wr_val : gprs[SI];
    di <= wr_en && !is_8_bit && wr_sel == DI ? wr_val : gprs[DI];
    bp <= wr_en && !is_8_bit && wr_sel == BP ? wr_val : gprs[BP];

    bx <= gprs[BX];
    if (wr_en && !is_8_bit && wr_sel == BX)
        bx <= wr_val;
    if (wr_en && is_8_bit && wr_sel == BL)
        bx <= {gprs[BX][15:8], wr_val[7:0]};
    if (wr_en && is_8_bit && wr_sel == BH)
        bx <= {wr_val[7:0], gprs[BX][7:0]};
end

// Read port 0
always_ff @(posedge clk or posedge reset) begin
    if (reset)
        rd_val[0] <= 16'h0000;
    else if (is_8_bit) begin
        if (wr_en && wr_sel == rd_sel[0])
            rd_val[0] <= {8'b0, wr_val[7:0]};
        else if (~rd_sel[0][2])
            rd_val[0] <= {8'b0, gprs[{1'b0, rd_sel[0][1:0]}][7:0]};
        else
            rd_val[0] <= {8'b0, gprs[{1'b0, rd_sel[0][1:0]}][15:8]};
    end else begin
        if (wr_en && wr_sel == rd_sel[0])
            rd_val[0] <= wr_val;
        else
            rd_val[0] <= gprs[rd_sel[0]];
    end
end

// Read port 1
always_ff @(posedge clk or posedge reset) begin
    if (reset)
        rd_val[1] <= 16'h0000;
    else if (is_8_bit) begin
        if (wr_en && wr_sel == rd_sel[1])
            rd_val[1] <= {8'b0, wr_val[7:0]};
        else if (~rd_sel[1][2])
            rd_val[1] <= {8'b0, gprs[{1'b0, rd_sel[1][1:0]}][7:0]};
        else
            rd_val[1] <= {8'b0, gprs[{1'b0, rd_sel[1][1:0]}][15:8]};
    end else begin
        if (wr_en && wr_sel == rd_sel[1])
            rd_val[1] <= wr_val;
        else
            rd_val[1] <= gprs[rd_sel[1]];
    end
end

endmodule
