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

    // Use a small cache for tractable proofs
    DCache2Way #(.sets(4)) dut (
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

    // Simple abstract memory model (word-addressed)
    logic [15:0] abs_mem [0:31];

    // Capture last CPU write data/addr for the current line
    logic [19:1] last_cpu_addr;
    logic [15:0] last_cpu_data;
    logic last_cpu_wr;

    // Track whether we are flushing and the line base being flushed
    logic flushing_line;
    logic [19:1] flush_base;

`ifdef FORMAL_TIGHT_ENV
    // Tight environment for fast convergence
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // ack implies access
        if (!$past(reset) && m_ack)
            assume($past(m_access));
        // single outstanding CPU access
        assume(c_access |-> ##1 !c_access);
        // bounded mem latency (1-2 cycles)
        assume(m_access && !m_ack |-> ##[1:2] m_ack);
        // full-word writes only
        assume(c_bytesel == 2'b11);
        // small address window
        assume(c_addr < 19'h0040);
    end
`else
    // Looser environment (only ack implies access)
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (!$past(reset) && m_ack)
            assume($past(m_access));
    end
`endif

    // Safety properties
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // No data ACK without an active access.
        assert(!c_ack || c_access);

        // Backend writes only occur when a memory access is active.
        assert(!m_wr_en || m_access);
    end

    // Track last CPU write
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (c_access && c_wr_en && c_ack) begin
            last_cpu_addr <= c_addr;
            last_cpu_data <= c_data_out;
            last_cpu_wr   <= 1'b1;
        end
    end

    // Abstract memory update on backend write
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (m_access && m_wr_en && m_ack) begin
            abs_mem[m_addr[12:1]] <= m_data_out;
        end
    end

    // Track flush region: when flushing, m_addr should span a single line
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (m_access && m_wr_en && busy_flush_line) begin end
    end

    // Helper: detect a write-back burst for one line (8 words) and ensure addresses are contiguous
    reg busy_flush_line;
    reg [19:1] flush_base_line;
    reg [2:0]  flush_beat;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            busy_flush_line  <= 1'b0;
            flush_base_line  <= 19'h0;
            flush_beat       <= 3'b0;
        end else if (seen_reset) begin
            if (!busy_flush_line && m_access && m_wr_en) begin
                busy_flush_line <= 1'b1;
                flush_base_line <= {m_addr[19:3], 3'b000};
                flush_beat      <= m_addr[2:0];
            end else if (busy_flush_line && m_access && m_wr_en && m_ack) begin
                // assert contiguous addresses within the same line
                assert(m_addr[19:3] == flush_base_line[19:3]);
                flush_beat <= flush_beat + 1'b1;
                if (flush_beat == 3'b111) begin
                    busy_flush_line <= 1'b0;
                end
            end
        end
    end

    // Property: If a CPU write hits (c_ack && c_wr_en) and eventually the line is flushed (backend writes that line),
    // then the abstract memory holds the last CPU data for that word.
    // This is a coarse property; we approximate by checking that any m_wr_en during a flush uses m_data_out == last_cpu_data
    // when addresses match last_cpu_addr.
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (m_access && m_wr_en && m_ack && last_cpu_wr) begin
            if (m_addr == last_cpu_addr)
                assert(m_data_out == last_cpu_data);
        end
    end

    // No write-back outside the current line during a contiguous flush burst
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (busy_flush_line && m_access && m_wr_en && m_ack) begin
            assert(m_addr[19:3] == flush_base_line[19:3]);
        end
    end

endmodule
