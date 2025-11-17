// Formal harness for Quartus/rtl/IDArbiter.sv

`default_nettype none

module IDArbiter_formal(
    input logic clk
);
    // Clock and reset
    logic reset;

    // Instruction bus
    (* anyseq *) logic [19:1] instr_m_addr;
    (* anyseq *) logic [15:0] instr_m_data_out;
    (* anyseq *) logic        instr_m_access;
    (* anyseq *) logic        instr_m_wr_en;
    (* anyseq *) logic [1:0]  instr_m_bytesel;
    logic [15:0]              instr_m_data_in;
    logic                     instr_m_ack;

    // Data bus
    (* anyseq *) logic [19:1] data_m_addr;
    (* anyseq *) logic [15:0] data_m_data_out;
    (* anyseq *) logic        data_m_access;
    (* anyseq *) logic        data_m_wr_en;
    (* anyseq *) logic [1:0]  data_m_bytesel;
    logic [15:0]              data_m_data_in;
    logic                     data_m_ack;

    // Shared memory bus
    logic [19:1]              q_m_addr;
    (* anyseq *) logic [15:0] q_m_data_in;
    logic [15:0]              q_m_data_out;
    logic                     q_m_access;
    (* anyseq *) logic        q_m_ack;
    logic                     q_m_wr_en;
    logic [1:0]               q_m_bytesel;
    logic                     q_b;

    // DUT
    IDArbiter dut (
        .clk(clk),
        .reset(reset),

        .instr_m_addr(instr_m_addr),
        .instr_m_data_in(instr_m_data_in),
        .instr_m_data_out(instr_m_data_out),
        .instr_m_access(instr_m_access),
        .instr_m_ack(instr_m_ack),
        .instr_m_wr_en(instr_m_wr_en),
        .instr_m_bytesel(instr_m_bytesel),

        .data_m_addr(data_m_addr),
        .data_m_data_in(data_m_data_in),
        .data_m_data_out(data_m_data_out),
        .data_m_access(data_m_access),
        .data_m_ack(data_m_ack),
        .data_m_wr_en(data_m_wr_en),
        .data_m_bytesel(data_m_bytesel),

        .q_m_addr(q_m_addr),
        .q_m_data_in(q_m_data_in),
        .q_m_data_out(q_m_data_out),
        .q_m_access(q_m_access),
        .q_m_ack(q_m_ack),
        .q_m_wr_en(q_m_wr_en),
        .q_m_bytesel(q_m_bytesel),
        .q_b(q_b)
    );

    // Reset sequencing
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

    // Environment assumption
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (!$past(reset) && q_m_ack)
            assume($past(q_m_access));
    end

    // Safety properties
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // Never acknowledge both instruction and data in the same cycle.
        assert(!(instr_m_ack && data_m_ack));

        // Any master ACK must coincide with a shared-bus ACK.
        if (instr_m_ack)
            assert(q_m_ack);
        if (data_m_ack)
            assert(q_m_ack);
    end

endmodule

