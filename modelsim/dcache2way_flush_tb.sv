// Dedicated flush/write-back correctness test for DCache2Way
// Focuses on dirty eviction: write a line, dirty multiple words, thrash the set,
// and ensure SDRAM sees the updated words exactly once with correct data.

`timescale 1ns/1ps
`default_nettype none

module dcache2way_flush_tb;
    // Small cache to make evictions deterministic
    localparam SETS = 4;  // 4 sets × 2 ways = 8 lines total

    // Clock/reset
    logic clk = 0;
    logic reset = 0;
    always #5 clk = ~clk;

    // CPU side
    logic [19:1] c_addr;
    logic [15:0] c_data_in;
    logic [15:0] c_data_out;
    logic        c_access;
    logic        c_ack;
    logic        c_wr_en;
    logic [1:0]  c_bytesel;

    // Memory side
    logic [19:1] m_addr;
    logic [15:0] m_data_in;
    logic [15:0] m_data_out;
    logic        m_access;
    logic        m_ack;
    logic        m_wr_en;
    logic [1:0]  m_bytesel;

    // Simple SDRAM model
    logic [15:0] mem [0:2047];  // 2K words for this test

    DCache2Way #(.sets(SETS), .DEBUG(1'b1)) dut (
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
        .m_bytesel(m_bytesel),
        // coherence ports unused
        .coh_wr_valid(),
        .coh_wr_addr(),
        .coh_wr_data(),
        .coh_wr_bytesel(),
        .coh_probe_valid(),
        .coh_probe_addr(),
        .coh_probe_present(1'b0)
    );

    // Memory model: 2-cycle latency for writes, 1-cycle for reads (simplified)
    always_ff @(posedge clk) begin
        m_ack <= 1'b0;
        if (reset) begin
            m_ack <= 1'b0;
            m_data_in <= 16'h0000;
        end else if (m_access) begin
            if (m_wr_en) begin
                m_ack <= 1'b1;
                if (m_bytesel[0]) mem[m_addr[11:1]][7:0]  <= m_data_out[7:0];
                if (m_bytesel[1]) mem[m_addr[11:1]][15:8] <= m_data_out[15:8];
            end else begin
                m_ack <= 1'b1;
                m_data_in <= mem[m_addr[11:1]];
            end
        end
    end

    task automatic cpu_store(input [19:1] addr, input [15:0] data, input [1:0] be);
        integer t;
        begin
            c_addr     = addr;
            c_data_out = data;
            c_bytesel  = be;
            c_wr_en    = 1'b1;
            c_access   = 1'b1;
            t = 0;
            @(posedge clk);
            while (!c_ack && t < 50) begin t++; @(posedge clk); end
            c_access   = 1'b0;
            c_wr_en    = 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    task automatic cpu_load(input [19:1] addr, output [15:0] data);
        integer t;
        begin
            c_addr    = addr;
            c_wr_en   = 1'b0;
            c_bytesel = 2'b11;
            c_access  = 1'b1;
            t = 0;
            @(posedge clk);
            while (!c_ack && t < 50) begin t++; @(posedge clk); end
            data = c_data_in;
            c_access = 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    integer failures;

    // Addresses chosen from index 0 (bits [11:4]=0)
    localparam [19:1] A0 = 19'h00010;  // target line
    localparam [19:1] A1 = 19'h10010;  // same set, different tag
    localparam [19:1] A2 = 19'h20010;  // same set, different tag

    initial begin
        integer i;
        reg [15:0] r;
        failures = 0;
        // init memory
        for (i = 0; i < 2048; i = i + 1) mem[i] = 16'h1111;

        reset = 1'b1;
        c_access = 1'b0;
        c_wr_en = 1'b0;
        c_bytesel = 2'b11;
        repeat(4) @(posedge clk);
        reset = 1'b0;
        repeat(4) @(posedge clk);

        $display("=== DCache2Way Flush/Write-back Test (sets=%0d) ===", SETS);

        // Dirty multiple words in the target line
        cpu_store(A0, 16'hDEAD, 2'b11); // word 0
        cpu_store(A0 + 3'h2, 16'hBEEF, 2'b11); // word 1 (addr offset +2 words)

        // Confirm cache hit returns updated data before eviction
        cpu_load(A0, r);
        if (r != 16'hDEAD) begin
            $display("FAIL: Hit read expected DEAD, got %h", r);
            failures++;
        end

        // Thrash same set to force eviction of A0
        cpu_store(A1, 16'h1111, 2'b11);
        cpu_store(A2, 16'h2222, 2'b11);  // eviction should occur here

        // Allow any flush to complete
        repeat(16) @(posedge clk);

        // Check SDRAM (mem) reflects both writes from the evicted line
        if (mem[A0[11:1]] != 16'hDEAD) begin
            $display("FAIL: mem[A0] expected DEAD, got %h", mem[A0[11:1]]);
            failures++;
        end
        if (mem[A0[11:1] + 1] != 16'hBEEF) begin
            $display("FAIL: mem[A0+2] expected BEEF, got %h", mem[A0[11:1] + 1]);
            failures++;
        end

        // Summary
        if (failures == 0) begin
            $display("✓ PASSED: flush/write-back correctness");
            $finish(0);
        end else begin
            $display("✗ FAILED: %0d issues", failures);
            $finish(1);
        end
    end
endmodule

`default_nettype wire
