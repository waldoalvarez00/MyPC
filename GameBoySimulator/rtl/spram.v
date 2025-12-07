//
// Single-Port RAM Module (Verilog replacement for spram.vhd)
//
// Copyright (c) 2024 - MIT License
//

module spram #(
    parameter addr_width = 8,
    parameter data_width = 8
) (
    input                       clock,
    input  [addr_width-1:0]     address,
    input  [data_width-1:0]     data,
    input                       wren,
    output reg [data_width-1:0] q
);

    // Memory array
    reg [data_width-1:0] mem [0:(2**addr_width)-1];

    always @(posedge clock) begin
        if (wren) begin
            mem[address] <= data;
        end
        q <= mem[address];
    end

endmodule
