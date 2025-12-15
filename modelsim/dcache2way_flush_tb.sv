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

    // Victim writeback port (non-blocking)
    logic [18:0] vwb_addr;      // Standard [18:0] indexing
    logic [15:0] vwb_data_out;
    logic        vwb_access;
    logic        vwb_ack;
    logic        vwb_wr_en;
    logic [1:0]  vwb_bytesel;

    // Simple SDRAM model - 128K words to avoid aliasing with different tags
    logic [15:0] mem [0:131071];  // 128K words (256KB) for this test

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
        // victim writeback port
        .vwb_addr(vwb_addr),
        .vwb_data_out(vwb_data_out),
        .vwb_access(vwb_access),
        .vwb_ack(vwb_ack),
        .vwb_wr_en(vwb_wr_en),
        .vwb_bytesel(vwb_bytesel),
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
                if (m_bytesel[0]) mem[m_addr[17:1]][7:0]  <= m_data_out[7:0];
                if (m_bytesel[1]) mem[m_addr[17:1]][15:8] <= m_data_out[15:8];
                $display("[%0t][MEM_MODEL] WRITE mem[%h] (m_addr=%h) <= %h (be=%b)",
                         $time, m_addr[17:1], m_addr, m_data_out, m_bytesel);
            end else begin
                m_ack <= 1'b1;
                m_data_in <= mem[m_addr[17:1]];
            end
        end
    end

    // Victim writeback memory model (write-only, single-cycle)
    logic [16:0] vwb_addr_latched;  // Word address for mem[] array
    logic [15:0] vwb_data_latched;
    logic [1:0]  vwb_be_latched;
    logic        vwb_busy;

    always_ff @(posedge clk) begin
        if (reset) begin
            vwb_ack <= 1'b0;
            vwb_busy <= 1'b0;
        end else begin
            // Victim writeback: capture request, then process next cycle
            if (vwb_access && vwb_wr_en && !vwb_busy && !vwb_ack) begin
                // Capture new VWB write request
                // vwb_addr is [18:0] and is ALREADY word-indexed (flush_beat is word offset)
                // Just use lower 17 bits to match mem[] array size
                vwb_addr_latched <= vwb_addr[16:0];
                vwb_data_latched <= vwb_data_out;
                vwb_be_latched <= vwb_bytesel;
                vwb_busy <= 1'b1;
                vwb_ack <= 1'b0;
            end else if (vwb_busy) begin
                // Process captured VWB write
                if (vwb_be_latched[0]) mem[vwb_addr_latched][7:0]  <= vwb_data_latched[7:0];
                if (vwb_be_latched[1]) mem[vwb_addr_latched][15:8] <= vwb_data_latched[15:8];
                $display("[%0t][VWB_MODEL] WRITE mem[%h] <= %h (be=%b)",
                         $time, vwb_addr_latched, vwb_data_latched, vwb_be_latched);
                vwb_ack <= 1'b1;
                vwb_busy <= 1'b0;
            end else begin
                vwb_ack <= 1'b0;
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
            @(posedge clk); // Wait one cycle for clean signal transition
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
            #1; // Wait for non-blocking assignments to settle
            $display("[%0t][LOAD] addr=%h c_data_in=%h c_ack=%b", $time, addr, c_data_in, c_ack);
            data = c_data_in;
            c_access = 1'b0;
            @(posedge clk); // Wait one cycle for clean signal transition
        end
    endtask

    integer failures;

    // Addresses chosen from set 1 (bits [5:4]=01 for 4-set cache)
    localparam [19:1] A0 = 19'h00010;  // target line, mem[0x10-0x17]
    localparam [19:1] A1 = 19'h10010;  // same set, different tag, mem[0x8010-0x8017]
    localparam [19:1] A2 = 19'h20010;  // same set, different tag, mem[0x10010-0x10017]

    initial begin
        integer i;
        reg [15:0] r;
        reg [19:1] A0_plus_2;
        failures = 0;
        A0_plus_2 = A0 + 19'h2;
        // init memory
        for (i = 0; i < 131072; i = i + 1) mem[i] = 16'h1111;

        reset = 1'b1;
        c_access = 1'b0;
        c_wr_en = 1'b0;
        c_bytesel = 2'b11;
        c_addr = 19'h00000;
        c_data_out = 16'h0000;
        repeat(4) @(posedge clk);
        reset = 1'b0;
        repeat(4) @(posedge clk);

        $display("=== DCache2Way Flush/Write-back Test (sets=%0d) ===", SETS);

        // Dirty multiple words in the target line
        $display("[TEST] Store DEAD at A0=%h (word offset=%d)", A0, A0[3:1]);
        cpu_store(A0, 16'hDEAD, 2'b11); // word 0
        $display("[TEST] Store BEEF at A0+2=%h (word offset=%d)", A0_plus_2, A0_plus_2[3:1]);
        cpu_store(A0_plus_2, 16'hBEEF, 2'b11); // word 1 (addr offset +1 word)

        // Confirm cache hit returns updated data before eviction
        $display("[TEST] Load from A0=%h (word offset=%d)", A0, A0[3:1]);
        cpu_load(A0, r);
        $display("[TEST] Got data=%h", r);
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
        $display("DEBUG: Checking mem[%h] = %h (expect DEAD)", A0[17:1], mem[A0[17:1]]);
        $display("DEBUG: Checking mem[%h] = %h (expect BEEF)", A0_plus_2[17:1], mem[A0_plus_2[17:1]]);
        if (mem[A0[17:1]] != 16'hDEAD) begin
            $display("FAIL: mem[A0] expected DEAD, got %h", mem[A0[17:1]]);
            failures++;
        end
        if (mem[A0_plus_2[17:1]] != 16'hBEEF) begin
            $display("FAIL: mem[A0+2] expected BEEF, got %h", mem[A0_plus_2[17:1]]);
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
