// Flattened formal-only clone of Quartus/rtl/CPU/RegisterFile.sv
// This avoids SystemVerilog unpacked array ports that Yosys 0.59
// cannot parse, while preserving the original behavior.

`default_nettype none
module RegisterFile_flat(
    input  logic        clk,
    input  logic        reset,
    input  logic        is_8_bit,
    output logic [15:0] si,
    output logic [15:0] di,
    output logic [15:0] bp,
    output logic [15:0] bx,
    // Flattened read ports.
    input  logic [2:0]  rd_sel0,
    input  logic [2:0]  rd_sel1,
    output logic [15:0] rd_val0,
    output logic [15:0] rd_val1,
    // Write port.
    input  logic [2:0]  wr_sel,
    input  logic [15:0] wr_val,
    input  logic        wr_en
);

    reg [15:0] gprs[8];

    wire wr_sel_low_byte = ~wr_sel[2];
    wire [2:0] wr_8_bit_sel = {1'b0, wr_sel[1:0]};

    // Reset is handled by the microcode in the original design.
    // Preserve the empty async reset block for equivalence.
    always_ff @(posedge reset)
        ;

    // Write port logic.
    always_ff @(posedge clk) begin
        if (wr_en) begin
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

    // Architectural register outputs.
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

    // Read port 0.
    wire rd0_sel_low_byte = ~rd_sel0[2];
    wire [2:0] rd0_8_bit_sel = {1'b0, rd_sel0[1:0]};
    wire bypass0 = wr_en && wr_sel == rd_sel0;

    always_ff @(posedge clk) begin
        if (is_8_bit)
            rd_val0 <= bypass0 ? {8'b0, wr_val[7:0]} :
                {8'b0, rd0_sel_low_byte ?
                    gprs[rd0_8_bit_sel][7:0] : gprs[rd0_8_bit_sel][15:8]};
        else
            rd_val0 <= bypass0 ? wr_val :
                gprs[rd_sel0];
    end

    // Read port 1.
    wire rd1_sel_low_byte = ~rd_sel1[2];
    wire [2:0] rd1_8_bit_sel = {1'b0, rd_sel1[1:0]};
    wire bypass1 = wr_en && wr_sel == rd_sel1;

    always_ff @(posedge clk) begin
        if (is_8_bit)
            rd_val1 <= bypass1 ? {8'b0, wr_val[7:0]} :
                {8'b0, rd1_sel_low_byte ?
                    gprs[rd1_8_bit_sel][7:0] : gprs[rd1_8_bit_sel][15:8]};
        else
            rd_val1 <= bypass1 ? wr_val :
                gprs[rd_sel1];
    end

endmodule

