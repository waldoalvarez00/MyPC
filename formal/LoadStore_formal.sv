// Formal harness for Quartus/rtl/CPU/LoadStore.sv

`default_nettype none

module LoadStore_formal(
    input clk
);
    // Clock and reset
    reg reset;

    // Memory Address Register interface
    (* anyseq *) reg        write_mar;
    (* anyseq *) reg [15:0] segment;
    (* anyseq *) reg [15:0] mar_in;
    wire [15:0]             mar_out;

    // Memory Data Register interface
    wire [15:0]             mdr_out;
    (* anyseq *) reg        write_mdr;
    (* anyseq *) reg [15:0] mdr_in;

    // Memory bus
    wire [19:1]             m_addr;
    (* anyseq *) reg [15:0] m_data_in;
    wire [15:0]             m_data_out;
    wire                    m_access;
    (* anyseq *) reg        m_ack;
    wire                    m_wr_en;
    wire [1:0]              m_bytesel;

    // Control
    (* anyseq *) reg        io;
    (* anyseq *) reg        mem_read;
    (* anyseq *) reg        mem_write;
    (* anyseq *) reg        is_8bit;
    (* anyseq *) reg        wr_en;
    wire                    busy;

    // DUT
    LoadStore dut (
        .clk(clk),
        .reset(reset),

        .write_mar(write_mar),
        .segment(segment),
        .mar_in(mar_in),

        .mar_out(mar_out),
        .mdr_out(mdr_out),
        .write_mdr(write_mdr),
        .mdr_in(mdr_in),

        .m_addr(m_addr),
        .m_data_in(m_data_in),
        .m_data_out(m_data_out),
        .m_access(m_access),
        .m_ack(m_ack),
        .m_wr_en(m_wr_en),
        .m_bytesel(m_bytesel),

        .io(io),
        .mem_read(mem_read),
        .mem_write(mem_write),
        .is_8bit(is_8bit),
        .wr_en(wr_en),
        .busy(busy)
    );

    // Basic reset: start in reset, then release
    initial reset = 1'b1;

    reg seen_reset;

    always @(posedge clk) begin
        if ($initstate) begin
            reset      <= 1'b1;
            seen_reset <= 1'b0;
        end else begin
            reset      <= 1'b0;
            if (reset)
                seen_reset <= 1'b1;
        end
    end

    // Environment assumptions
    always @(posedge clk) if (seen_reset && !reset) begin
        // Memory only acknowledges when a transaction is active.
        if (!$past(reset) && m_ack)
            assume($past(m_access));
    end

    // Safety properties
    always @(posedge clk) if (seen_reset && !reset) begin
        // Busy can only be asserted when a memory operation is requested.
        assert(!busy || (mem_read || mem_write));

        // If no memory operation is requested, busy must be deasserted.
        assert(!(busy && !mem_read && !mem_write));
    end

endmodule

