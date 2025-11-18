// Minimal Harvard I/D cache self-modifying code testbench
// Uses tiny caches and a single-cycle SDRAM model, no VGA path.
// Goal: isolate SMC correctness (D write → dirty eviction → I refetch).

`timescale 1ns/1ps
`default_nettype none

module harvard_smc_mini_tb;
    // Tiny caches to force evictions quickly
    localparam SETS = 4;  // 4 sets × 2 ways

    logic clk = 0;
    logic reset = 0;
    always #5 clk = ~clk;

    // CPU I-side
    logic [19:1] i_addr;
    logic [15:0] i_data_in;
    logic        i_access;
    logic        i_ack;

    // CPU D-side
    logic [19:1] d_addr;
    logic [15:0] d_data_in;
    logic [15:0] d_data_out;
    logic        d_access;
    logic        d_ack;
    logic        d_wr_en;
    logic [1:0]  d_bytesel;

    // I-cache backend
    logic [19:1] ic_m_addr;
    logic [15:0] ic_m_data_in;
    logic        ic_m_access;
    logic        ic_m_ack;

    // D-cache backend
    logic [19:1] dc_m_addr;
    logic [15:0] dc_m_data_in;
    logic [15:0] dc_m_data_out;
    logic        dc_m_access;
    logic        dc_m_ack;
    logic        dc_m_wr_en;
    logic [1:0]  dc_m_bytesel;

    // Unified bus after arbiter
    logic [19:1] mem_addr;
    logic [15:0] mem_data_out;
    logic [15:0] mem_data_in;
    logic        mem_access;
    logic        mem_ack;
    logic        mem_wr_en;
    logic [1:0]  mem_bytesel;

    // I-cache invalidation tap (unused; driven by mem arbiter if present)
    logic        ic_inval_valid;
    logic [19:1] ic_inval_addr;

    // Stub VGA signals (unused)
    logic vga_idle = 1'b0;

    // Simple SDRAM model
    logic [15:0] sdram [0:2047];

    // DUTs
    ICache2Way #(.sets(SETS)) icache (
        .clk(clk),
        .reset(reset),
        .enabled(1'b1),
        .c_addr(i_addr),
        .c_data_in(i_data_in),
        .c_access(i_access),
        .c_ack(i_ack),
        .m_addr(ic_m_addr),
        .m_data_in(ic_m_data_in),
        .m_access(ic_m_access),
        .m_ack(ic_m_ack),
        .inval_valid(ic_inval_valid),
        .inval_addr(ic_inval_addr),
        // coherence sideband off
        .coh_wr_valid(1'b0),
        .coh_wr_addr(19'b0),
        .coh_wr_data(16'b0),
        .coh_wr_bytesel(2'b0),
        .coh_probe_valid(1'b0),
        .coh_probe_addr(19'b0),
        .coh_probe_present(/* unused */)
    );

    DCache2Way #(.sets(SETS), .DEBUG(1'b1)) dcache (
        .clk(clk),
        .reset(reset),
        .enabled(1'b1),
        .c_addr(d_addr),
        .c_data_in(d_data_in),
        .c_data_out(d_data_out),
        .c_access(d_access),
        .c_ack(d_ack),
        .c_wr_en(d_wr_en),
        .c_bytesel(d_bytesel),
        .m_addr(dc_m_addr),
        .m_data_in(dc_m_data_in),
        .m_data_out(dc_m_data_out),
        .m_access(dc_m_access),
        .m_ack(dc_m_ack),
        .m_wr_en(dc_m_wr_en),
        .m_bytesel(dc_m_bytesel),
        // coherence sideband off
        .coh_wr_valid(),
        .coh_wr_addr(),
        .coh_wr_data(),
        .coh_wr_bytesel(),
        .coh_probe_valid(),
        .coh_probe_addr(),
        .coh_probe_present(1'b0)
    );

    // Arbiter: simple round-robin between I and D
    CacheArbiter arb (
        .clk(clk),
        .reset(reset),
        .icache_m_addr(ic_m_addr),
        .icache_m_data_in(ic_m_data_in),
        .icache_m_access(ic_m_access),
        .icache_m_ack(ic_m_ack),
        .dcache_m_addr(dc_m_addr),
        .dcache_m_data_in(dc_m_data_in),
        .dcache_m_data_out(dc_m_data_out),
        .dcache_m_access(dc_m_access),
        .dcache_m_ack(dc_m_ack),
        .dcache_m_wr_en(dc_m_wr_en),
        .dcache_m_bytesel(dc_m_bytesel),
        .mem_m_addr(mem_addr),
        .mem_m_data_in(mem_data_in),
        .mem_m_data_out(mem_data_out),
        .mem_m_access(mem_access),
        .mem_m_ack(mem_ack),
        .mem_m_wr_en(mem_wr_en),
        .mem_m_bytesel(mem_bytesel)
    );

    // Single-cycle SDRAM model
    always_ff @(posedge clk) begin
        mem_ack <= 1'b0;
        if (reset) begin
            mem_ack <= 1'b0;
            mem_data_in <= 16'h0000;
        end else if (mem_access) begin
            mem_ack <= 1'b1;
            if (mem_wr_en) begin
                if (mem_bytesel[0]) sdram[mem_addr[11:1]][7:0]  <= mem_data_out[7:0];
                if (mem_bytesel[1]) sdram[mem_addr[11:1]][15:8] <= mem_data_out[15:8];
            end else begin
                mem_data_in <= sdram[mem_addr[11:1]];
            end
        end
    end

    // State helpers
    task automatic do_fetch(input [19:1] addr, output [15:0] data);
        integer t;
        begin
            i_addr   <= addr;
            i_access <= 1'b1;
            t = 0;
            @(posedge clk);
            while (!i_ack && t < 50) begin t++; @(posedge clk); end
            data = i_data_in;
            i_access <= 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    task automatic do_store(input [19:1] addr, input [15:0] data, input [1:0] be);
        integer t;
        begin
            d_addr     <= addr;
            d_data_out <= data;
            d_bytesel  <= be;
            d_wr_en    <= 1'b1;
            d_access   <= 1'b1;
            t = 0;
            @(posedge clk);
            while (!d_ack && t < 50) begin t++; @(posedge clk); end
            d_access   <= 1'b0;
            d_wr_en    <= 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    integer test_count, pass_count, fail_count;
    task automatic check(input bit cond, input string msg);
        begin
            test_count++;
            if (cond) begin
                pass_count++;
                $display("  ✓ %s", msg);
            end else begin
                fail_count++;
                $display("  ✗ %s", msg);
            end
        end
    endtask

    initial begin
        integer i;
        test_count = 0; pass_count = 0; fail_count = 0;
        // init SDRAM
        for (i = 0; i < 2048; i = i + 1) sdram[i] = 16'h0000;

        reset = 1'b1;
        i_access = 1'b0;
        d_access = 1'b0;
        d_wr_en  = 1'b0;
        d_bytesel= 2'b11;
        repeat(4) @(posedge clk);
        reset = 1'b0;
        repeat(4) @(posedge clk);

        $display("=== Harvard SMC Mini Test (sets=%0d) ===", SETS);

        // Choose addresses mapping to same set (index=0)
        localparam [19:1] A0 = 19'h00010; // target code
        localparam [19:1] A1 = 19'h10010; // same set, other tag
        localparam [19:1] A2 = 19'h20010; // same set, other tag

        // Initialize SDRAM contents
        sdram[A0[11:1]] = 16'h1111;
        sdram[A1[11:1]] = 16'h2222;
        sdram[A2[11:1]] = 16'h3333;

        // Step 1: I-fetch original code
        automatic [15:0] q;
        do_fetch(A0, q);
        check(q == 16'h1111, "Initial I-fetch sees original code");

        // Step 2: D-store new code
        do_store(A0, 16'hDEAD, 2'b11);
        // Local D readback
        do_fetch(A0, q);
        check(q == 16'hDEAD, "D-side readback sees updated code");

        // Step 3: Force eviction of A0 by touching A1,A2
        do_store(A1, 16'hBEEF, 2'b11);
        do_store(A2, 16'hCAFE, 2'b11);
        repeat(8) @(posedge clk);

        // Check SDRAM now holds updated code
        check(sdram[A0[11:1]] == 16'hDEAD, "SDRAM holds updated code after eviction");

        // Step 4: I-fetch should see updated code
        do_fetch(A0, q);
        check(q == 16'hDEAD, "I-fetch after eviction sees updated code");

        $display("Summary: %0d tests, %0d pass, %0d fail", test_count, pass_count, fail_count);
        if (fail_count == 0) begin
            $finish(0);
        end else begin
            $finish(1);
        end
    end
endmodule

`default_nettype wire
