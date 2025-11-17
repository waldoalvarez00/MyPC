// Formal harness for Quartus/rtl/CPU/RegisterFile.sv

`default_nettype none

module RegisterFile_formal(
    input clk
);
    // Inputs
    (* anyseq *) reg        reset;
    (* anyseq *) reg        is_8_bit;
    (* anyseq *) reg [2:0]  rd_sel0;
    (* anyseq *) reg [2:0]  rd_sel1;
    (* anyseq *) reg [2:0]  wr_sel;
    (* anyseq *) reg [15:0] wr_val;
    (* anyseq *) reg        wr_en;

    // Outputs
    wire [15:0] rd_val0;
    wire [15:0] rd_val1;

    // Architectural outputs (not directly used in properties, but wired)
    wire [15:0] si, di, bp, bx;

    // DUT: flattened formal-only clone
    RegisterFile_flat dut (
        .clk(clk),
        .reset(reset),
        .is_8_bit(is_8_bit),
        .si(si),
        .di(di),
        .bp(bp),
        .bx(bx),
        .rd_sel0(rd_sel0),
        .rd_sel1(rd_sel1),
        .rd_val0(rd_val0),
        .rd_val1(rd_val1),
        .wr_sel(wr_sel),
        .wr_val(wr_val),
        .wr_en(wr_en)
    );

    // Safety properties: bypass behavior on the same cycle as a write.
    always @(posedge clk) begin
        // Port 0
        if (wr_en && !is_8_bit && (rd_sel0 == wr_sel))
            assert(rd_val0 == wr_val);

        if (wr_en && is_8_bit && (rd_sel0 == wr_sel))
            assert(rd_val0 == {8'b0, wr_val[7:0]});

        // Port 1
        if (wr_en && !is_8_bit && (rd_sel1 == wr_sel))
            assert(rd_val1 == wr_val);

        if (wr_en && is_8_bit && (rd_sel1 == wr_sel))
            assert(rd_val1 == {8'b0, wr_val[7:0]});
    end

endmodule
