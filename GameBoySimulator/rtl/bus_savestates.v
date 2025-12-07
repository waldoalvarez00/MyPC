//
// Savestate Bus Package and Register Module
// (Verilog replacement for bus_savestates.vhd)
//
// Copyright (c) 2024 - MIT License
//

// eReg_SavestateV - Verbose savestate register with explicit parameters
module eReg_SavestateV #(
    parameter index = 0,
    parameter Adr   = 0,
    parameter upper = 63,
    parameter lower = 0,
    parameter [63:0] def = 64'h0
) (
    input         clk,
    input  [63:0] BUS_Din,
    input  [9:0]  BUS_Adr,
    input         BUS_wren,
    input         BUS_rst,
    output [63:0] BUS_Dout,
    input  [upper:lower] Din,
    output reg [upper:lower] Dout
);

    wire [9:0] AdrI = Adr + index;

    // Output buffer register
    initial begin
        Dout = def[upper:lower];
    end

    always @(posedge clk) begin
        if (BUS_rst) begin
            Dout <= def[upper:lower];
        end
        else if (BUS_Adr == AdrI && BUS_wren) begin
            Dout <= BUS_Din[upper:lower];
        end
    end

    // Bus output - only drive when addressed, else 0
    genvar i;
    generate
        for (i = 0; i < 64; i = i + 1) begin : gen_bus_out
            if (i >= lower && i <= upper) begin
                assign BUS_Dout[i] = (BUS_Adr == AdrI) ? Din[i] : 1'b0;
            end else begin
                assign BUS_Dout[i] = 1'b0;
            end
        end
    endgenerate

endmodule
