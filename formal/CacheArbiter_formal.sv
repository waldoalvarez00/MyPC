// Formal harness for Quartus/rtl/common/CacheArbiter.sv
//
// Ensures mutual exclusion and proper propagation of ACKs.

`default_nettype none

module CacheArbiter_formal(
    input logic clk
);
    logic reset;

    // I-Cache backend
    (* anyseq *) logic [19:1] icache_m_addr;
    logic [15:0]              icache_m_data_in;
    (* anyseq *) logic        icache_m_access;
    logic                     icache_m_ack;

    // D-Cache backend
    (* anyseq *) logic [19:1] dcache_m_addr;
    logic [15:0]              dcache_m_data_in;
    (* anyseq *) logic [15:0] dcache_m_data_out;
    (* anyseq *) logic        dcache_m_access;
    logic                     dcache_m_ack;
    (* anyseq *) logic        dcache_m_wr_en;
    (* anyseq *) logic [1:0]  dcache_m_bytesel;

    // Memory side
    logic [19:1]              mem_m_addr;
    (* anyseq *) logic [15:0] mem_m_data_in;
    logic [15:0]              mem_m_data_out;
    logic                     mem_m_access;
    (* anyseq *) logic        mem_m_ack;
    logic                     mem_m_wr_en;
    logic [1:0]               mem_m_bytesel;

    CacheArbiter dut (
        .clk(clk),
        .reset(reset),
        .icache_m_addr(icache_m_addr),
        .icache_m_data_in(icache_m_data_in),
        .icache_m_access(icache_m_access),
        .icache_m_ack(icache_m_ack),
        .dcache_m_addr(dcache_m_addr),
        .dcache_m_data_in(dcache_m_data_in),
        .dcache_m_data_out(dcache_m_data_out),
        .dcache_m_access(dcache_m_access),
        .dcache_m_ack(dcache_m_ack),
        .dcache_m_wr_en(dcache_m_wr_en),
        .dcache_m_bytesel(dcache_m_bytesel),
        .mem_m_addr(mem_m_addr),
        .mem_m_data_in(mem_m_data_in),
        .mem_m_data_out(mem_m_data_out),
        .mem_m_access(mem_m_access),
        .mem_m_ack(mem_m_ack),
        .mem_m_wr_en(mem_m_wr_en),
        .mem_m_bytesel(mem_m_bytesel)
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
        if (!$past(reset) && mem_m_ack)
            assume($past(mem_m_access));
    end

    // Safety properties
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // At most one cache can see an ACK in any cycle.
        assert(!(icache_m_ack && dcache_m_ack));

        // Any ACK to a cache must coincide with a memory ACK.
        if (icache_m_ack)
            assert(mem_m_ack);
        if (dcache_m_ack)
            assert(mem_m_ack);
    end

endmodule

