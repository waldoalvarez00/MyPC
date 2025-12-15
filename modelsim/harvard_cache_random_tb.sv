// Randomized Harvard cache integration test with golden memory scoreboard
// Uses tiny caches and a simple SDRAM model to catch incoherent behavior in mixed I-fetch/D-load/D-store traffic.

`timescale 1ns/1ps
`default_nettype none

module harvard_cache_random_tb;
    localparam SETS = 4;  // small to force evictions
    localparam MEM_DEPTH = 1024;

    logic clk = 0;
    always #5 clk = ~clk;
    logic reset = 0;

    // CPU instruction side
    logic [19:1] i_addr;
    logic [15:0] i_data_in;
    logic        i_access;
    logic        i_ack;

    // CPU data side
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

    // Memory bus after arbiter
    logic [19:1] mem_addr;
    logic [15:0] mem_data_in;
    logic [15:0] mem_data_out;
    logic        mem_access;
    logic        mem_ack;
    logic        mem_wr_en;
    logic [1:0]  mem_bytesel;

    // Inval tap (unused)
    logic        ic_inval_valid;
    logic [19:1] ic_inval_addr;

    // Coherence signals between D-cache and I-cache
    logic        coh_wr_valid;
    logic [19:1] coh_wr_addr;
    logic [15:0] coh_wr_data;
    logic [1:0]  coh_wr_bytesel;
    logic        coh_probe_valid;
    logic [19:1] coh_probe_addr;
    logic        coh_probe_present;

    // SDRAM model and golden memory
    logic [15:0] sdram [0:MEM_DEPTH-1];
    logic [15:0] golden[0:MEM_DEPTH-1];

    // DUTs
    ICache2Way #(.sets(SETS)) icache (
        .clk(clk), .reset(reset), .enabled(1'b1),
        .c_addr(i_addr), .c_data_in(i_data_in),
        .c_access(i_access), .c_ack(i_ack),
        .m_addr(ic_m_addr), .m_data_in(ic_m_data_in),
        .m_access(ic_m_access), .m_ack(ic_m_ack),
        .inval_valid(ic_inval_valid), .inval_addr(ic_inval_addr),
        .coh_wr_valid(coh_wr_valid), .coh_wr_addr(coh_wr_addr),
        .coh_wr_data(coh_wr_data), .coh_wr_bytesel(coh_wr_bytesel),
        .coh_probe_valid(coh_probe_valid), .coh_probe_addr(coh_probe_addr),
        .coh_probe_present(coh_probe_present)
    );

    DCache2Way #(.sets(SETS)) dcache (
        .clk(clk), .reset(reset), .enabled(1'b1),
        .c_addr(d_addr), .c_data_in(d_data_in),
        .c_data_out(d_data_out), .c_access(d_access),
        .c_ack(d_ack), .c_wr_en(d_wr_en), .c_bytesel(d_bytesel),
        .m_addr(dc_m_addr), .m_data_in(dc_m_data_in),
        .m_data_out(dc_m_data_out), .m_access(dc_m_access),
        .m_ack(dc_m_ack), .m_wr_en(dc_m_wr_en), .m_bytesel(dc_m_bytesel),
        .coh_wr_valid(coh_wr_valid), .coh_wr_addr(coh_wr_addr), .coh_wr_data(coh_wr_data),
        .coh_wr_bytesel(coh_wr_bytesel), .coh_probe_valid(coh_probe_valid), .coh_probe_addr(coh_probe_addr),
        .coh_probe_present(coh_probe_present)
    );

    CacheArbiter arb (
        .clk(clk), .reset(reset),
        .icache_m_addr(ic_m_addr), .icache_m_data_in(ic_m_data_in),
        .icache_m_access(ic_m_access), .icache_m_ack(ic_m_ack),
        .dcache_m_addr(dc_m_addr), .dcache_m_data_in(dc_m_data_in),
        .dcache_m_data_out(dc_m_data_out), .dcache_m_access(dc_m_access),
        .dcache_m_ack(dc_m_ack), .dcache_m_wr_en(dc_m_wr_en),
        .dcache_m_bytesel(dc_m_bytesel),
        .mem_m_addr(mem_addr), .mem_m_data_in(mem_data_in),
        .mem_m_data_out(mem_data_out), .mem_m_access(mem_access),
        .mem_m_ack(mem_ack), .mem_m_wr_en(mem_wr_en),
        .mem_m_bytesel(mem_bytesel)
    );

    // SDRAM: 1-cycle latency
    always_ff @(posedge clk) begin
        mem_ack <= 1'b0;
        if (reset) begin
            mem_ack <= 1'b0;
            mem_data_in <= 16'h0000;
        end else if (mem_access) begin
            mem_ack <= 1'b1;
            if (mem_wr_en) begin
                if (mem_bytesel[0]) sdram[mem_addr[10:1]][7:0]  <= mem_data_out[7:0];
                if (mem_bytesel[1]) sdram[mem_addr[10:1]][15:8] <= mem_data_out[15:8];
            end else begin
                mem_data_in <= sdram[mem_addr[10:1]];
            end
        end
    end

    // Golden memory update on every store (CPU-side)
    task automatic golden_write(input [19:1] addr, input [15:0] data, input [1:0] be);
        begin
            if (be[0]) golden[addr[10:1]][7:0]  = data[7:0];
            if (be[1]) golden[addr[10:1]][15:8] = data[15:8];
        end
    endtask

    task automatic do_ifetch(input [19:1] addr, output [15:0] data);
        integer t;
        begin
            i_addr = addr;
            i_access = 1'b1;
            t = 0;
            @(posedge clk);
            while (!i_ack && t < 50) begin t++; @(posedge clk); end
            #1; // Wait for non-blocking assignments to settle
            data = i_data_in;
            i_access = 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    task automatic do_dstore(input [19:1] addr, input [15:0] data, input [1:0] be);
        integer t;
        begin
            d_addr = addr;
            d_data_out = data;
            d_bytesel = be;
            d_wr_en = 1'b1;
            d_access = 1'b1;
            t = 0;
            @(posedge clk);
            while (!d_ack && t < 50) begin t++; @(posedge clk); end
            d_access = 1'b0;
            d_wr_en = 1'b0;
            repeat(1) @(posedge clk);
            golden_write(addr, data, be);
        end
    endtask

    task automatic do_dload(input [19:1] addr, output [15:0] data);
        integer t;
        begin
            d_addr = addr;
            d_wr_en = 1'b0;
            d_bytesel = 2'b11;
            d_access = 1'b1;
            t = 0;
            @(posedge clk);
            while (!d_ack && t < 50) begin t++; @(posedge clk); end
            #1; // Wait for non-blocking assignments to settle
            data = d_data_in;
            d_access = 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    integer failures, ops;
    reg [15:0] q;

    initial begin
        integer i;
        failures = 0;
        for (i = 0; i < MEM_DEPTH; i = i + 1) begin
            sdram[i]  = 16'h0000;
            golden[i] = 16'h0000;
        end
        reset = 1'b1;
        i_access = 1'b0;
        d_access = 1'b0;
        d_wr_en  = 1'b0;
        d_bytesel= 2'b11;
        ic_inval_valid = 1'b0;
        ic_inval_addr = 19'b0;
        repeat(4) @(posedge clk);
        reset = 1'b0;
        repeat(4) @(posedge clk);

        $display("=== Harvard Cache Random Coherence Test (SETS=%0d) ===", SETS);
        ops = 0;
        repeat (200) begin
            ops++;
            // simple pseudo-random operation mix
            case ($urandom_range(0,2))
                0: begin // I-fetch
                    reg [19:1] a = {9'h0, $urandom_range(0, MEM_DEPTH-1), 1'b0};
                    do_ifetch(a, q);
                    if (q !== golden[a[10:1]]) begin
                        $display("FAIL[%0d]: IFETCH addr=%h got=%h exp=%h", ops, a, q, golden[a[10:1]]);
                        failures++;
                    end
                end
                1: begin // D-store full word
                    reg [19:1] a = {9'h0, $urandom_range(0, MEM_DEPTH-1), 1'b0};
                    reg [15:0] d = $urandom;
                    do_dstore(a, d, 2'b11);
                end
                2: begin // D-load
                    reg [19:1] a = {9'h0, $urandom_range(0, MEM_DEPTH-1), 1'b0};
                    do_dload(a, q);
                    if (q !== golden[a[10:1]]) begin
                        $display("FAIL[%0d]: DLOAD addr=%h got=%h exp=%h", ops, a, q, golden[a[10:1]]);
                        failures++;
                    end
                end
            endcase
        end

        if (failures == 0) begin
            $display("✓ PASSED: Harvard cache random coherence");
            $finish(0);
        end else begin
            $display("✗ FAILED: %0d mismatches", failures);
            $finish(1);
        end
    end
endmodule

`default_nettype wire
