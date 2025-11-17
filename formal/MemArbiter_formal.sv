// Formal harness for Quartus/rtl/CPU/MemArbiter.sv

`default_nettype none

module MemArbiter_formal(
    input clk
);
    // Clock and reset
    reg reset;

    // Instruction bus
    (* anyseq *) reg  [19:1] a_m_addr;
    (* anyseq *) reg  [15:0] a_m_data_out;
    (* anyseq *) reg         a_m_access;
    (* anyseq *) reg         a_m_wr_en;
    (* anyseq *) reg  [1:0]  a_m_bytesel;
    wire [15:0] a_m_data_in;
    wire        a_m_ack;

    // Data bus
    (* anyseq *) reg  [19:1] b_m_addr;
    (* anyseq *) reg  [15:0] b_m_data_out;
    (* anyseq *) reg         b_m_access;
    (* anyseq *) reg         b_m_wr_en;
    (* anyseq *) reg  [1:0]  b_m_bytesel;
    wire [15:0] b_m_data_in;
    wire        b_m_ack;

    // Shared memory bus
    wire [19:1] q_m_addr;
    (* anyseq *) reg  [15:0] q_m_data_in;
    wire [15:0] q_m_data_out;
    wire        q_m_access;
    (* anyseq *) reg         q_m_ack;
    wire        q_m_wr_en;
    wire [1:0]  q_m_bytesel;
    wire        q_b;

    // DUT
    MemArbiter dut (
        .clk(clk),
        .reset(reset),

        .a_m_addr(a_m_addr),
        .a_m_data_in(a_m_data_in),
        .a_m_data_out(a_m_data_out),
        .a_m_access(a_m_access),
        .a_m_ack(a_m_ack),
        .a_m_wr_en(a_m_wr_en),
        .a_m_bytesel(a_m_bytesel),

        .b_m_addr(b_m_addr),
        .b_m_data_in(b_m_data_in),
        .b_m_data_out(b_m_data_out),
        .b_m_access(b_m_access),
        .b_m_ack(b_m_ack),
        .b_m_wr_en(b_m_wr_en),
        .b_m_bytesel(b_m_bytesel),

        .q_m_addr(q_m_addr),
        .q_m_data_in(q_m_data_in),
        .q_m_data_out(q_m_data_out),
        .q_m_access(q_m_access),
        .q_m_ack(q_m_ack),
        .q_m_wr_en(q_m_wr_en),
        .q_m_bytesel(q_m_bytesel),
        .q_b(q_b)
    );

    // Basic reset: start in reset, then release
    initial reset = 1'b1;

    always @(posedge clk) begin
        if ($initstate)
            reset <= 1'b1;
        else
            reset <= 1'b0;
    end

    // Keep writes and read-only accesses well-formed
    always @(posedge clk) begin
        if (!reset) begin
            // No X / Z propagation in formal model
            assume(a_m_bytesel != 2'bxx);
            assume(b_m_bytesel != 2'bxx);
        end
    end

    // Environment assumptions:
    //  - Memory only acknowledges when an access is active.
    //  - Masters hold access high until they see ACK.
    reg seen_reset;
    always @(posedge clk) begin
        if ($initstate)
            seen_reset <= 1'b0;
        else if (reset)
            seen_reset <= 1'b1;

        if (seen_reset && !reset) begin
            // Memory only acks when arbiter has an active transaction.
            if (!$past(reset) && q_m_ack)
                assume($past(q_m_access));

            // Access lines are stable until acknowledged.
            if ($past(a_m_access && !a_m_ack))
                assume(a_m_access);
            if ($past(b_m_access && !b_m_ack))
                assume(b_m_access);
        end
    end

    // Safety properties
    always @(posedge clk) if (seen_reset && !reset) begin
        // Never ACK both instruction and data bus in the same cycle.
        assert(!(a_m_ack && b_m_ack));

        // Any ACK must come from an active memory acknowledgement.
        if (a_m_ack)
            assert(q_m_ack);
        if (b_m_ack)
            assert(q_m_ack);

        // When an ACK is issued, the corresponding master must have
        // been requesting access in the previous cycle.
        if (!$past(reset)) begin
            if (a_m_ack)
                assert($past(a_m_access));
            if (b_m_ack)
                assert($past(b_m_access));
        end

        // If the data bus is acknowledged, it must be the selected bus.
        if (b_m_ack)
            assert(q_b);

        // If the instruction bus is acknowledged, it must be selected.
        if (a_m_ack)
            assert(!q_b);

        // When there is no request, the shared bus must not assert access.
        assert(!(q_m_access && !(a_m_access || b_m_access)));
    end

endmodule
