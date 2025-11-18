// Formal harness: Small DCache2Way + PipelinedMemArbiterExtend
// Goal: any D-side write that is eventually evicted/forwarded reaches SDRAM
// with the last CPU data for that address (no lost writes).

`default_nettype none

module DCache2Way_MemArbiter_formal(input logic clk);
    logic reset;

    // CPU side (data only in this harness)
    (* anyseq *) logic [19:1] c_addr;
    (* anyseq *) logic [15:0] c_data_out;
    (* anyseq *) logic        c_access;
    (* anyseq *) logic        c_wr_en;
    (* anyseq *) logic [1:0]  c_bytesel;
    logic [15:0]              c_data_in;
    logic                     c_ack;

    // DCache -> arbiter
    logic [19:1] dc_m_addr;
    logic [15:0] dc_m_data_in;
    logic [15:0] dc_m_data_out;
    logic        dc_m_access;
    logic        dc_m_ack;
    logic        dc_m_wr_en;
    logic [1:0]  dc_m_bytesel;

    // ICache not instantiated; mem arbiter CPU port is driven by D-cache only
    // VGA path unused
    logic [19:1] dummy_addr;
    logic [15:0] dummy_data_in;
    logic [15:0] dummy_data_out;
    logic        dummy_access;
    logic        dummy_ack;
    logic        dummy_wr_en;
    logic [1:0]  dummy_bytesel;

    // SDRAM interface
    logic [19:1] sdram_addr;
    (* anyseq *) logic [15:0] sdram_data_in;
    logic [15:0] sdram_data_out;
    logic        sdram_access;
    (* anyseq *) logic        sdram_ack;
    logic        sdram_wr_en;
    logic [1:0]  sdram_bytesel;

    // I-cache inval taps (unused)
    logic icache_inval_valid;
    logic [19:1] icache_inval_addr;

    // Small DCache for tractability
    DCache2Way #(.sets(4)) dcache (
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
        .m_addr(dc_m_addr),
        .m_data_in(dc_m_data_in),
        .m_data_out(dc_m_data_out),
        .m_access(dc_m_access),
        .m_ack(dc_m_ack),
        .m_wr_en(dc_m_wr_en),
        .m_bytesel(dc_m_bytesel),
        .coh_wr_valid(), .coh_wr_addr(), .coh_wr_data(),
        .coh_wr_bytesel(), .coh_probe_valid(), .coh_probe_addr(),
        .coh_probe_present(1'b0)
    );

    // Arbiter (no VGA, I-port unused)
    PipelinedMemArbiterExtend #(.DEBUG(1'b0)) arb (
        .clk(clk),
        .reset(reset),
        .cpu_m_addr(dc_m_addr),
        .cpu_m_data_in(dc_m_data_in),
        .cpu_m_data_out(dc_m_data_out),
        .cpu_m_access(dc_m_access),
        .cpu_m_ack(dc_m_ack),
        .cpu_m_wr_en(dc_m_wr_en),
        .cpu_m_bytesel(dc_m_bytesel),
        .mcga_m_addr(19'b0),
        .mcga_m_data_in(dummy_data_in),
        .mcga_m_data_out(16'b0),
        .mcga_m_access(1'b0),
        .mcga_m_ack(dummy_ack),
        .mcga_m_wr_en(1'b0),
        .mcga_m_bytesel(2'b00),
        .vga_active_display(1'b0),
        .icache_inval_valid(icache_inval_valid),
        .icache_inval_addr(icache_inval_addr),
        .sdram_m_addr(sdram_addr),
        .sdram_m_data_in(sdram_data_in),
        .sdram_m_data_out(sdram_data_out),
        .sdram_m_access(sdram_access),
        .sdram_m_ack(sdram_ack),
        .sdram_m_wr_en(sdram_wr_en),
        .sdram_m_bytesel(sdram_bytesel),
        .q_b()
    );

    // Abstract SDRAM model (word-addressed)
    logic [15:0] abs_sdram [0:31];

    // Reset sequencing
    initial reset = 1'b1;
    logic seen_reset;
    always_ff @(posedge clk) begin
        if ($initstate) begin
            reset <= 1'b1;
            seen_reset <= 1'b0;
        end else begin
            reset <= 1'b0;
            if (reset)
                seen_reset <= 1'b1;
        end
    end

    // Environment: ack implies access
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (!$past(reset) && sdram_ack)
            assume($past(sdram_access));
    end

    // Abstract SDRAM update on write
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (sdram_access && sdram_wr_en && sdram_ack) begin
            abs_sdram[sdram_addr[12:1]] <= sdram_data_out;
        end
    end

    // Track last CPU write request
    logic [19:1] last_cpu_addr;
    logic [15:0] last_cpu_data;
    logic        last_cpu_wr;
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (c_access && c_wr_en && c_ack) begin
            last_cpu_addr <= c_addr;
            last_cpu_data <= c_data_out;
            last_cpu_wr   <= 1'b1;
        end
    end

    // Property: when SDRAM write occurs to last_cpu_addr, it must carry last_cpu_data
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (sdram_access && sdram_wr_en && sdram_ack && last_cpu_wr) begin
            if (sdram_addr == last_cpu_addr)
                assert(sdram_data_out == last_cpu_data);
        end
    end

    // Property: no write-back to unrelated addresses during burst flush
    // (approximated: if two consecutive write backs, they must share the same line tag/index)
    reg [19:1] prev_wb_addr;
    reg        prev_wb_valid;
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (sdram_access && sdram_wr_en && sdram_ack) begin
            if (prev_wb_valid)
                assert(prev_wb_addr[19:3] == sdram_addr[19:3]);
            prev_wb_addr  <= sdram_addr;
            prev_wb_valid <= 1'b1;
        end else if (!$past(sdram_access && sdram_wr_en && sdram_ack))
            prev_wb_valid <= 1'b0;
    end

    // Safety: no backend write without CPU access
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        assert(!sdram_wr_en || sdram_access);
    end

endmodule

`default_nettype wire
