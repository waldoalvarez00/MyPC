// ================================================================
// Wrapper for RegisterFile to handle Icarus Verilog unpacked array issue
// Icarus doesn't properly expose rd_sel[2] and rd_val[2] array ports
// This wrapper flattens them to scalar ports
// ================================================================

`default_nettype none
module RegisterFile_wrapper(
    input logic clk,
    input logic reset,
    input logic is_8_bit,
    output logic [15:0] si,
    output logic [15:0] di,
    output logic [15:0] bp,
    output logic [15:0] bx,
    // Flattened read port 0
    input logic [2:0] rd_sel_0,
    output logic [15:0] rd_val_0,
    // Flattened read port 1
    input logic [2:0] rd_sel_1,
    output logic [15:0] rd_val_1,
    // Write port
    input logic [2:0] wr_sel,
    input logic [15:0] wr_val,
    input logic wr_en
);

// Internal array signals
logic [2:0] rd_sel [2];
logic [15:0] rd_val [2];

// Connect flattened ports to arrays
assign rd_sel[0] = rd_sel_0;
assign rd_sel[1] = rd_sel_1;
assign rd_val_0 = rd_val[0];
assign rd_val_1 = rd_val[1];

// Instantiate actual RegisterFile
RegisterFile uut (
    .clk(clk),
    .reset(reset),
    .is_8_bit(is_8_bit),
    .si(si),
    .di(di),
    .bp(bp),
    .bx(bx),
    .rd_sel(rd_sel),
    .rd_val(rd_val),
    .wr_sel(wr_sel),
    .wr_val(wr_val),
    .wr_en(wr_en)
);

endmodule
