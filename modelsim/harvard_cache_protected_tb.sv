// Protected-address coherency test: ensure never-written address stays zero
// while other traffic thrashes the cache. Uses small caches and golden memory.

`timescale 1ns/1ps
`default_nettype none

module harvard_cache_protected_tb;
    localparam SETS = 4;
    localparam MEM_DEPTH = 512;

    logic clk = 0;
    always #5 clk = ~clk;
    logic reset = 0;

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

    // D-cache backend - main port
    logic [19:1] dc_m_addr;
    logic [15:0] dc_m_data_in;
    logic [15:0] dc_m_data_out;
    logic        dc_m_access;
    logic        dc_m_ack;
    logic        dc_m_wr_en;
    logic [1:0]  dc_m_bytesel;

    // D-cache backend - victim writeback port
    logic [19:1] dc_vwb_addr;
    logic [15:0] dc_vwb_data_out;
    logic        dc_vwb_access;
    logic        dc_vwb_ack;
    logic        dc_vwb_wr_en;
    logic [1:0]  dc_vwb_bytesel;

    // Memory bus
    logic [19:1] mem_addr;
    logic [15:0] mem_data_in;
    logic [15:0] mem_data_out;
    logic        mem_access;
    logic        mem_ack;
    logic        mem_wr_en;
    logic [1:0]  mem_bytesel;

    logic        ic_inval_valid;
    logic [19:1] ic_inval_addr;

    // Memories
    logic [15:0] sdram [0:MEM_DEPTH-1];
    logic [15:0] golden[0:MEM_DEPTH-1];

    localparam [19:1] PROT = 19'h00100; // protected address (never written)

    ICache2Way #(.sets(SETS)) icache (
        .clk(clk), .reset(reset), .enabled(1'b1),
        .c_addr(i_addr), .c_data_in(i_data_in),
        .c_access(i_access), .c_ack(i_ack),
        .m_addr(ic_m_addr), .m_data_in(ic_m_data_in),
        .m_access(ic_m_access), .m_ack(ic_m_ack),
        .inval_valid(ic_inval_valid), .inval_addr(ic_inval_addr),
        .coh_wr_valid(1'b0), .coh_wr_addr(19'b0),
        .coh_wr_data(16'b0), .coh_wr_bytesel(2'b00),
        .coh_probe_valid(1'b0), .coh_probe_addr(19'b0),
        .coh_probe_present()
    );

    DCache2Way #(.sets(SETS), .DEBUG(1'b1)) dcache (
        .clk(clk), .reset(reset), .enabled(1'b1),
        .c_addr(d_addr), .c_data_in(d_data_in),
        .c_data_out(d_data_out), .c_access(d_access),
        .c_ack(d_ack), .c_wr_en(d_wr_en), .c_bytesel(d_bytesel),
        .m_addr(dc_m_addr), .m_data_in(dc_m_data_in),
        .m_data_out(dc_m_data_out), .m_access(dc_m_access),
        .m_ack(dc_m_ack), .m_wr_en(dc_m_wr_en), .m_bytesel(dc_m_bytesel),
        .vwb_addr(dc_vwb_addr), .vwb_data_out(dc_vwb_data_out),
        .vwb_access(dc_vwb_access), .vwb_ack(dc_vwb_ack),
        .vwb_wr_en(dc_vwb_wr_en), .vwb_bytesel(dc_vwb_bytesel),
        .coh_wr_valid(), .coh_wr_addr(), .coh_wr_data(),
        .coh_wr_bytesel(), .coh_probe_valid(), .coh_probe_addr(),
        .coh_probe_present(1'b0)
    );

    HarvardArbiter3Way arb (
        .clk(clk), .reset(reset),
        .icache_m_addr(ic_m_addr), .icache_m_data_in(ic_m_data_in),
        .icache_m_access(ic_m_access), .icache_m_ack(ic_m_ack),
        .dcache_m_addr(dc_m_addr), .dcache_m_data_in(dc_m_data_in),
        .dcache_m_data_out(dc_m_data_out), .dcache_m_access(dc_m_access),
        .dcache_m_ack(dc_m_ack), .dcache_m_wr_en(dc_m_wr_en),
        .dcache_m_bytesel(dc_m_bytesel),
        .dcache_vwb_addr(dc_vwb_addr), .dcache_vwb_data_out(dc_vwb_data_out),
        .dcache_vwb_access(dc_vwb_access), .dcache_vwb_ack(dc_vwb_ack),
        .dcache_vwb_wr_en(dc_vwb_wr_en), .dcache_vwb_bytesel(dc_vwb_bytesel),
        .mem_m_addr(mem_addr), .mem_m_data_in(mem_data_in),
        .mem_m_data_out(mem_data_out), .mem_m_access(mem_access),
        .mem_m_ack(mem_ack), .mem_m_wr_en(mem_wr_en),
        .mem_m_bytesel(mem_bytesel)
    );

    // Simple SDRAM with comprehensive address tracking
    // FIX: Use combinatorial read to avoid one-cycle data latency
    localparam logic [19:1] PROT_ADDR = 19'h00100;

    // Combinatorial read path for zero-latency data
    assign mem_data_in = sdram[mem_addr[9:1]];

    always_ff @(posedge clk) begin
        mem_ack <= 1'b0;
        if (reset) begin
            mem_ack <= 1'b0;
        end else if (mem_access) begin
            mem_ack <= 1'b1;
            if (mem_wr_en) begin
                if (mem_bytesel[0]) sdram[mem_addr[9:1]][7:0]  <= mem_data_out[7:0];
                if (mem_bytesel[1]) sdram[mem_addr[9:1]][15:8] <= mem_data_out[15:8];
                // DEBUG: Track writes to PROT address line (0x00100-0x00107)
                if (mem_addr[19:4] == PROT_ADDR[19:4]) begin
                    $display("[%0t][SDRAM] WRITE addr=%h data=%h->%h be=%b idx=%0d",
                             $time, mem_addr, sdram[mem_addr[9:1]], mem_data_out, mem_bytesel, mem_addr[9:1]);
                end
            end else begin
                // DEBUG: Track reads from PROT address line (0x00100-0x00107)
                if (mem_addr[19:4] == PROT_ADDR[19:4]) begin
                    $display("[%0t][SDRAM] READ addr=%h data=%h idx=%0d",
                             $time, mem_addr, sdram[mem_addr[9:1]], mem_addr[9:1]);
                end
            end
        end
    end

    // Helpers
    task automatic golden_write(input [19:1] addr, input [15:0] data, input [1:0] be);
        begin
            // Write to golden array for verification
            if (be[0]) golden[addr[9:1]][7:0]  = data[7:0];
            if (be[1]) golden[addr[9:1]][15:8] = data[15:8];
            // ALSO write to SDRAM to initialize test data!
            if (be[0]) sdram[addr[9:1]][7:0]  = data[7:0];
            if (be[1]) sdram[addr[9:1]][15:8] = data[15:8];
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

    integer ops, failures;
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
        repeat(4) @(posedge clk);
        reset = 1'b0;
        repeat(4) @(posedge clk);

        $display("=== Harvard Cache Protected Address Test ===");
        ops = 0;
        repeat (200) begin
            ops++;
            // periodically check protected address
            if (ops % 10 == 0) begin
                do_ifetch(PROT, q);
                if (q !== 16'h0000) begin
                    $display("FAIL[%0d]: PROT IFETCH got=%h exp=0000", ops, q);
                    failures++;
                end
                do_dload(PROT, q);
                if (q !== 16'h0000) begin
                    $display("FAIL[%0d]: PROT DLOAD got=%h exp=0000", ops, q);
                    failures++;
                end
            end else begin
                // random op excluding PROT
                case ($urandom_range(0,2))
                    0: begin
                        reg [19:1] a;
                        a = {9'h0, $urandom_range(0, MEM_DEPTH-1), 1'b0};
                        if (a == PROT) a = a + 19'h2;
                        do_ifetch(a, q);
                        if (q !== golden[a[9:1]]) begin
                            $display("FAIL[%0d]: IFETCH addr=%h got=%h exp=%h", ops, a, q, golden[a[9:1]]);
                            failures++;
                        end
                    end
                    1: begin
                        reg [19:1] a;
                        reg [15:0] d;
                        a = {9'h0, $urandom_range(0, MEM_DEPTH-1), 1'b0};
                        if (a == PROT) a = a + 19'h2;
                        d = $urandom;
                        do_dstore(a, d, 2'b11);
                    end
                    2: begin
                        reg [19:1] a;
                        a = {9'h0, $urandom_range(0, MEM_DEPTH-1), 1'b0};
                        if (a == PROT) a = a + 19'h2;
                        do_dload(a, q);
                        if (q !== golden[a[9:1]]) begin
                            $display("FAIL[%0d]: DLOAD addr=%h got=%h exp=%h", ops, a, q, golden[a[9:1]]);
                            failures++;
                        end
                    end
                endcase
            end
        end

        if (failures == 0) begin
            $display("✓ PASSED: protected address stays coherent");
            $finish(0);
        end else begin
            $display("✗ FAILED: %0d mismatches", failures);
            $finish(1);
        end
    end
endmodule

`default_nettype wire
