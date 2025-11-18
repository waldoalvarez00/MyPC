// Formal harness for Quartus/rtl/common/DCache2Way.sv
//
// Checks basic handshake and write-back interface properties.

`default_nettype none

module DCache2Way_formal(
    input logic clk
);
    logic reset;

    // Frontend (CPU / unified data port in this harness)
    (* anyseq *) logic [19:1] c_addr;
    (* anyseq *) logic [15:0] c_data_out;
    (* anyseq *) logic        c_access;
    (* anyseq *) logic        c_wr_en;
    (* anyseq *) logic [1:0]  c_bytesel;
    logic [15:0]              c_data_in;
    logic                     c_ack;

    // Backend (memory)
    logic [19:1]              m_addr;
    (* anyseq *) logic [15:0] m_data_in;
    logic [15:0]              m_data_out;
    logic                     m_access;
    (* anyseq *) logic        m_ack;
    logic                     m_wr_en;
    logic [1:0]               m_bytesel;

    DCache2Way #(.sets(256)) dut (
        .clk(clk),
        .reset(reset),
        .enabled(1'b1),
        .c_addr(c_addr),
        .c_data_in(c_data_in),
        .c_data_out(c_data_out),
        .c_access(c_access),
        .c_ack(c_ack),
        .c_wr_en(c_wr_en),
        .c_bytesel(c_bytesel),
        .m_addr(m_addr),
        .m_data_in(m_data_in),
        .m_data_out(m_data_out),
        .m_access(m_access),
        .m_ack(m_ack),
        .m_wr_en(m_wr_en),
        .m_bytesel(m_bytesel)
    );

    initial reset = 1'b1;
    logic seen_reset;

    always_ff @(posedge clk) begin
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
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (!$past(reset) && m_ack)
            assume($past(m_access));
    end

    // Safety properties
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // No data ACK without an active access.
        assert(!c_ack || c_access);

        // Backend writes only occur when a memory access is active.
        assert(!m_wr_en || m_access);
    end

endmodule

