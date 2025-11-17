// Formal harness for Quartus/rtl/PipelinedDMAFPUArbiter.sv

`default_nettype none

module PipelinedDMAFPUArbiter_formal(
    input logic clk
);
    logic reset;

    // DMA bus (A)
    (* anyseq *) logic [19:1] a_m_addr;
    (* anyseq *) logic [15:0] a_m_data_out;
    (* anyseq *) logic        a_m_access;
    (* anyseq *) logic        a_m_wr_en;
    (* anyseq *) logic [1:0]  a_m_bytesel;
    (* anyseq *) logic        ioa;
    logic [15:0]              a_m_data_in;
    logic                     a_m_ack;

    // CPU cache bus (B)
    (* anyseq *) logic [19:1] b_m_addr;
    (* anyseq *) logic [15:0] b_m_data_out;
    (* anyseq *) logic        b_m_access;
    (* anyseq *) logic        b_m_wr_en;
    (* anyseq *) logic [1:0]  b_m_bytesel;
    (* anyseq *) logic        iob;
    logic [15:0]              b_m_data_in;
    logic                     b_m_ack;

    // FPU bus (C)
    (* anyseq *) logic [19:1] c_m_addr;
    (* anyseq *) logic [15:0] c_m_data_out;
    (* anyseq *) logic        c_m_access;
    (* anyseq *) logic        c_m_wr_en;
    (* anyseq *) logic [1:0]  c_m_bytesel;
    logic [15:0]              c_m_data_in;
    logic                     c_m_ack;

    // Shared bus
    logic [19:1]              q_m_addr;
    (* anyseq *) logic [15:0] q_m_data_in;
    logic [15:0]              q_m_data_out;
    logic                     q_m_access;
    (* anyseq *) logic        q_m_ack;
    logic                     q_m_wr_en;
    logic [1:0]               q_m_bytesel;
    logic                     ioq;
    logic [1:0]               q_grant;

    PipelinedDMAFPUArbiter dut (
        .clk(clk),
        .reset(reset),

        .a_m_addr(a_m_addr),
        .a_m_data_in(a_m_data_in),
        .a_m_data_out(a_m_data_out),
        .a_m_access(a_m_access),
        .a_m_ack(a_m_ack),
        .a_m_wr_en(a_m_wr_en),
        .a_m_bytesel(a_m_bytesel),
        .ioa(ioa),

        .b_m_addr(b_m_addr),
        .b_m_data_in(b_m_data_in),
        .b_m_data_out(b_m_data_out),
        .b_m_access(b_m_access),
        .b_m_ack(b_m_ack),
        .b_m_wr_en(b_m_wr_en),
        .b_m_bytesel(b_m_bytesel),
        .iob(iob),

        .c_m_addr(c_m_addr),
        .c_m_data_in(c_m_data_in),
        .c_m_data_out(c_m_data_out),
        .c_m_access(c_m_access),
        .c_m_ack(c_m_ack),
        .c_m_wr_en(c_m_wr_en),
        .c_m_bytesel(c_m_bytesel),

        .q_m_addr(q_m_addr),
        .q_m_data_in(q_m_data_in),
        .q_m_data_out(q_m_data_out),
        .q_m_access(q_m_access),
        .q_m_ack(q_m_ack),
        .q_m_wr_en(q_m_wr_en),
        .q_m_bytesel(q_m_bytesel),
        .ioq(ioq),
        .q_grant(q_grant)
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

    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (!$past(reset) && q_m_ack)
            assume($past(q_m_access));
    end

    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // Only one ACK at a time (or none).
        assert($onehot0({a_m_ack, b_m_ack, c_m_ack}));

        // Any master ACK must coincide with shared-bus ACK.
        if (a_m_ack)
            assert(q_m_ack);
        if (b_m_ack)
            assert(q_m_ack);
        if (c_m_ack)
            assert(q_m_ack);
    end

endmodule

