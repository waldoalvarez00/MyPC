// Formal harness for Quartus/rtl/common/ICache2Way.sv
//
// Focuses on handshake correctness and the new invalidation interface.

`default_nettype none

module ICache2Way_formal(
    input logic clk
);
    // Clock and reset
    logic reset;

    // Frontend (CPU fetch)
    (* anyseq *) logic [19:1] c_addr;
    (* anyseq *) logic        c_access;
    logic [15:0]              c_data_in;
    logic                     c_ack;

    // Backend (memory)
    logic [19:1]              m_addr;
    (* anyseq *) logic [15:0] m_data_in;
    logic                     m_access;
    (* anyseq *) logic        m_ack;

    // Invalidation (from D-side writes)
    (* anyseq *) logic        inval_valid;
    (* anyseq *) logic [19:1] inval_addr;

    ICache2Way #(.sets(256)) dut (
        .clk(clk),
        .reset(reset),
        .enabled(1'b1),
        .c_addr(c_addr),
        .c_data_in(c_data_in),
        .c_access(c_access),
        .c_ack(c_ack),
        .m_addr(m_addr),
        .m_data_in(m_data_in),
        .m_access(m_access),
        .m_ack(m_ack),
        .inval_valid(inval_valid),
        .inval_addr(inval_addr)
    );

    // Reset + simple environment
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
        // Memory ACKs only follow an asserted access.
        if (!$past(reset) && m_ack)
            assume($past(m_access));
    end

    // Safety properties
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // No instruction ACK without an active CPU access.
        assert(!c_ack || c_access);

        // Invalidation may occur at any time, but must not depend on reset.
        if (inval_valid)
            assert(!reset);
    end

endmodule

