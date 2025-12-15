// Harvard D-Cache Flush-Only Testbench
// ------------------------------------
// This testbench isolates the D-cache flush mechanism by:
//   - Using ONLY DCache2Way (no ICache) through the Harvard topology
//   - Testing that dirty line evictions correctly write back to SDRAM
//   - Helps localize whether failures are in "DCache flush" vs "ICache invalidation"
//
// This is a variant of harvard_smc_tb.sv that removes ICache to isolate issues.

`timescale 1ns/1ps
`default_nettype none

module harvard_dcache_flush_tb;

// Configurable cache size parameter
// Can be overridden via command line: +define+CACHE_SETS=4
// Small caches (2-4 sets) reveal replacement/flush bugs faster
`ifndef CACHE_SETS
    `define CACHE_SETS 256
`endif
parameter SETS = `CACHE_SETS;

// Clock and reset
logic clk;
logic reset;

// CPU data interface
logic [19:1] data_addr;
logic [15:0] data_data_in;
logic [15:0] data_data_out;
logic        data_access;
logic        data_ack;
logic        data_wr_en;
logic [1:0]  data_bytesel;

// D-Cache backend - main port
logic [19:1] dc_m_addr;
logic [15:0] dc_m_data_in;
logic [15:0] dc_m_data_out;
logic        dc_m_access;
logic        dc_m_ack;
logic        dc_m_wr_en;
logic [1:0]  dc_m_bytesel;

// D-Cache backend - victim writeback port
logic [18:0] dc_vwb_addr;  // Standard [18:0] indexing
logic [15:0] dc_vwb_data_out;
logic        dc_vwb_access;
logic        dc_vwb_ack;
logic        dc_vwb_wr_en;
logic [1:0]  dc_vwb_bytesel;

// Unified cache -> memory bus (HarvardArbiter3Way)
logic [19:1] cache_mem_addr;
logic [15:0] cache_mem_data_in;
logic [15:0] cache_mem_data_out;
logic        cache_mem_access;
logic        cache_mem_ack;
logic        cache_mem_wr_en;
logic [1:0]  cache_mem_bytesel;

// SDRAM interface (final arbiter)
logic [19:1] sdram_addr;
logic [15:0] sdram_data_in;
logic [15:0] sdram_data_out;
logic        sdram_access;
logic        sdram_ack;
logic        sdram_wr_en;
logic [1:0]  sdram_bytesel;

// I-cache invalidation tap (unused but required for arbiter)
logic        icache_inval_valid;
logic [19:1] icache_inval_addr;

// Coherence sideband (unused - no ICache)
logic        coh_wr_valid;
logic [19:1] coh_wr_addr;
logic [15:0] coh_wr_data;
logic [1:0]  coh_wr_bytesel;
logic        coh_probe_valid;
logic [19:1] coh_probe_addr;
logic        coh_probe_present;

// Simple SDRAM memory model (512K words)
logic [15:0] memory [0:524287];

// Test bookkeeping
integer test_count;
integer pass_count;
integer fail_count;

// ---------------------------------------------------------------------------
// DUT Instances (DCache only - no ICache)
// ---------------------------------------------------------------------------

// Data cache: 2-way set associative, write-back
DCache2Way #(.sets(SETS), .DEBUG(1'b1)) DCacheInst (
    .clk(clk),
    .reset(reset),
    .enabled(1'b1),
    // CPU side
    .c_addr(data_addr),
    .c_data_in(data_data_in),
    .c_data_out(data_data_out),
    .c_access(data_access),
    .c_ack(data_ack),
    .c_wr_en(data_wr_en),
    .c_bytesel(data_bytesel),
    // Memory side - main port
    .m_addr(dc_m_addr),
    .m_data_in(dc_m_data_in),
    .m_data_out(dc_m_data_out),
    .m_access(dc_m_access),
    .m_ack(dc_m_ack),
    .m_wr_en(dc_m_wr_en),
    .m_bytesel(dc_m_bytesel),
    // Memory side - victim writeback port
    .vwb_addr(dc_vwb_addr),
    .vwb_data_out(dc_vwb_data_out),
    .vwb_access(dc_vwb_access),
    .vwb_ack(dc_vwb_ack),
    .vwb_wr_en(dc_vwb_wr_en),
    .vwb_bytesel(dc_vwb_bytesel),
    // Coherence sideband (unused - tied off)
    .coh_wr_valid(coh_wr_valid),
    .coh_wr_addr(coh_wr_addr),
    .coh_wr_data(coh_wr_data),
    .coh_wr_bytesel(coh_wr_bytesel),
    .coh_probe_valid(coh_probe_valid),
    .coh_probe_addr(coh_probe_addr),
    .coh_probe_present(coh_probe_present)
);

// Tie off coherence probe (no ICache to respond)
assign coh_probe_present = 1'b0;

// Harvard arbiter with 3-way support: I-cache + D-cache main + D-cache VWB
// (I-cache side tied idle for this D-cache-only test)
HarvardArbiter3Way CacheArb (
    .clk(clk),
    .reset(reset),
    // I-cache interface (tied idle)
    .icache_m_addr(19'b0),
    .icache_m_data_in(),
    .icache_m_access(1'b0),
    .icache_m_ack(),
    // D-cache main interface
    .dcache_m_addr(dc_m_addr),
    .dcache_m_data_in(dc_m_data_in),
    .dcache_m_data_out(dc_m_data_out),
    .dcache_m_access(dc_m_access),
    .dcache_m_ack(dc_m_ack),
    .dcache_m_wr_en(dc_m_wr_en),
    .dcache_m_bytesel(dc_m_bytesel),
    // D-cache victim writeback interface
    .dcache_vwb_addr(dc_vwb_addr),
    .dcache_vwb_data_out(dc_vwb_data_out),
    .dcache_vwb_access(dc_vwb_access),
    .dcache_vwb_ack(dc_vwb_ack),
    .dcache_vwb_wr_en(dc_vwb_wr_en),
    .dcache_vwb_bytesel(dc_vwb_bytesel),
    // Unified memory interface
    .mem_m_addr(cache_mem_addr),
    .mem_m_data_in(cache_mem_data_in),
    .mem_m_data_out(cache_mem_data_out),
    .mem_m_access(cache_mem_access),
    .mem_m_ack(cache_mem_ack),
    .mem_m_wr_en(cache_mem_wr_en),
    .mem_m_bytesel(cache_mem_bytesel)
);

// Final SDRAM arbiter
PipelinedMemArbiterExtend #(.DEBUG(1'b1)) CacheVGAArb (
    .clk(clk),
    .reset(reset),
    // CPU+DMA bus from cache arbiter
    .cpu_m_addr(cache_mem_addr),
    .cpu_m_data_in(cache_mem_data_in),
    .cpu_m_data_out(cache_mem_data_out),
    .cpu_m_access(cache_mem_access),
    .cpu_m_ack(cache_mem_ack),
    .cpu_m_wr_en(cache_mem_wr_en),
    .cpu_m_bytesel(cache_mem_bytesel),
    // VGA bus (idle in this test)
    .mcga_m_addr(19'b0),
    .mcga_m_data_in(),
    .mcga_m_data_out(16'b0),
    .mcga_m_access(1'b0),
    .mcga_m_ack(),
    .mcga_m_wr_en(1'b0),
    .mcga_m_bytesel(2'b00),
    // VGA priority hint disabled
    .vga_active_display(1'b0),
    // I-cache invalidation tap (unused but present)
    .icache_inval_valid(icache_inval_valid),
    .icache_inval_addr(icache_inval_addr),
    // SDRAM interface
    .sdram_m_addr(sdram_addr),
    .sdram_m_data_in(sdram_data_in),
    .sdram_m_data_out(sdram_data_out),
    .sdram_m_access(sdram_access),
    .sdram_m_ack(sdram_ack),
    .sdram_m_wr_en(sdram_wr_en),
    .sdram_m_bytesel(sdram_bytesel),
    .q_b()
);

// ---------------------------------------------------------------------------
// Clock and SDRAM memory model
// ---------------------------------------------------------------------------

initial begin
    clk = 0;
    forever #5 clk = ~clk;  // 100 MHz
end

// Simple SDRAM model with 2-cycle latency
integer sdram_latency_cnt;
reg     sdram_pending;
localparam SDRAM_LATENCY = 2;

always_ff @(posedge clk) begin
    if (reset) begin
        sdram_ack        <= 1'b0;
        sdram_latency_cnt <= 0;
        sdram_pending    <= 1'b0;
        sdram_data_in    <= 16'b0;
    end else begin
        sdram_ack <= 1'b0;

        if (sdram_access && !sdram_pending) begin
            sdram_pending      <= 1'b1;
            sdram_latency_cnt  <= SDRAM_LATENCY;
        end else if (sdram_pending) begin
            if (sdram_latency_cnt > 1) begin
                sdram_latency_cnt <= sdram_latency_cnt - 1;
            end else begin
                sdram_pending <= 1'b0;
                sdram_ack     <= 1'b1;
                if (sdram_wr_en) begin
                    memory[sdram_addr] <= sdram_data_out;
                    $display("[SDRAM] WRITE addr=%h data=%h be=%b", sdram_addr, sdram_data_out, sdram_bytesel);
                end else begin
                    sdram_data_in <= memory[sdram_addr];
                    $display("[SDRAM] READ  addr=%h data=%h", sdram_addr, memory[sdram_addr]);
                end
            end
        end
    end
end

// ---------------------------------------------------------------------------
// Helper tasks
// ---------------------------------------------------------------------------

task automatic check(input bit cond, input string msg);
begin
    test_count++;
    if (cond) begin
        pass_count++;
        $display("[PASS] %0s", msg);
    end else begin
        fail_count++;
        $display("[FAIL] %0s", msg);
    end
end
endtask

// Data write via D-cache
task automatic data_write(input [19:1] addr,
                          input [15:0] wdata,
                          input [1:0]  bytesel,
                          output bit   success);
    integer timeout;
begin
    data_addr     = addr;
    data_data_out = wdata;
    data_wr_en    = 1'b1;
    data_bytesel  = bytesel;
    data_access   = 1'b1;
    success       = 1'b0;
    timeout       = 0;

    @(posedge clk);
    while (!data_ack && timeout < 200) begin
        @(posedge clk);
        timeout++;
    end

    if (data_ack)
        success = 1'b1;

    data_access = 1'b0;
    data_wr_en  = 1'b0;
    @(posedge clk);
end
endtask

// Data read via D-cache
task automatic data_read(input  [19:1] addr,
                         output [15:0] rdata,
                         output bit    success);
    integer timeout;
begin
    data_addr     = addr;
    data_wr_en    = 1'b0;
    data_bytesel  = 2'b11;
    data_access   = 1'b1;
    success       = 1'b0;
    timeout       = 0;

    @(posedge clk);
    while (!data_ack && timeout < 200) begin
        @(posedge clk);
        timeout++;
    end

    if (data_ack) begin
        rdata   = data_data_in;
        success = 1'b1;
    end

    data_access = 1'b0;
    @(posedge clk);
end
endtask

// ---------------------------------------------------------------------------
// Test sequence: D-cache flush isolation test
// ---------------------------------------------------------------------------

initial begin
    integer i;
    reg [15:0] data;
    bit success;

    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    // Initialize SDRAM contents
    for (i = 0; i < 524288; i = i + 1)
        memory[i] = 16'h0000;

    // Specific addresses that map to the same D-cache set:
    //  - 0x00300 : target address to modify
    //  - 0x01300, 0x02300 : additional lines in same set to force eviction
    memory[19'h00300] = 16'h1111;
    memory[19'h01300] = 16'h2222;
    memory[19'h02300] = 16'h3333;

    // Reset
    reset        = 1'b1;
    data_addr    = 19'h0;
    data_access  = 1'b0;
    data_wr_en   = 1'b0;
    data_bytesel = 2'b11;
    data_data_out = 16'h0;

    repeat(10) @(posedge clk);
    reset = 1'b0;
    repeat(10) @(posedge clk);

    $display("[DBG] Initial SDRAM contents:");
    $display("  mem[00300]=%h mem[01300]=%h mem[02300]=%h",
             memory[19'h00300], memory[19'h01300], memory[19'h02300]);

    $display("==================================================");
    $display("Harvard D-Cache Flush-Only Test");
    $display("DCache2Way + CacheArbiter + PipelinedMemArbiterExtend");
    $display("(No ICache - isolates flush mechanism)");
    $display("Cache Configuration: SETS = %0d", SETS);
    $display("==================================================");

    // -----------------------------------------------------------------------
    // Test 1: Basic write and readback
    // -----------------------------------------------------------------------
    $display("\n--- Test 1: Basic D-cache write and readback ---");

    $display("\n[FLUSH] Step 1a: Read initial value from 0x00300");
    data_read(19'h00300, data, success);
    check(success && data == 16'h1111,
          $sformatf("Initial read returns 0x%04h (expected 0x1111)", data));

    $display("\n[FLUSH] Step 1b: Write new value (0xDEAD) to 0x00300");
    data_write(19'h00300, 16'hDEAD, 2'b11, success);
    check(success, "D-cache write completed");

    $display("\n[FLUSH] Step 1c: Read back from 0x00300");
    data_read(19'h00300, data, success);
    check(success && data == 16'hDEAD,
          $sformatf("D-cache readback sees 0x%04h (expected 0xDEAD)", data));

    // ASSERTION: Readback must work before testing flush
    if (!success || data != 16'hDEAD) begin
        $display("[FATAL] Test 1 FAILED: D-cache readback expected 0xDEAD, got 0x%04h", data);
        $display("        This is a basic D-cache read/write failure");
        $fatal(1, "Basic D-cache operation failed");
    end
    $display("[ASSERT] Test 1 PASSED: Basic D-cache operations working");

    // -----------------------------------------------------------------------
    // Test 2: Force eviction and check SDRAM write-back
    // -----------------------------------------------------------------------
    $display("\n--- Test 2: Force dirty line eviction ---");

    $display("\n[FLUSH] Step 2a: Write to 0x01300 (same set as 0x00300)");
    data_write(19'h01300, 16'hBEEF, 2'b11, success);
    check(success, "D-cache write at 0x01300 completed");

    $display("\n[FLUSH] Step 2b: Write to 0x02300 (triggers eviction of 0x00300)");
    data_write(19'h02300, 16'hCAFE, 2'b11, success);
    check(success, "D-cache write at 0x02300 completed");

    // Allow time for write-back pipeline to complete
    repeat(60) @(posedge clk);

    // Check SDRAM contents after eviction
    $display("\n[FLUSH] Step 2c: Verify SDRAM contents after eviction");
    $display("  SDRAM[00300] = 0x%04h (expected 0xDEAD)", memory[19'h00300]);
    $display("  SDRAM[01300] = 0x%04h", memory[19'h01300]);
    $display("  SDRAM[02300] = 0x%04h", memory[19'h02300]);

    check(memory[19'h00300] == 16'hDEAD,
          $sformatf("SDRAM[00300] = 0x%04h after eviction", memory[19'h00300]));

    // CRITICAL ASSERTION: This is the main flush test
    if (memory[19'h00300] != 16'hDEAD) begin
        $display("[FATAL] Test 2 FAILED: SDRAM at 0x00300 expected 0xDEAD, got 0x%04h", memory[19'h00300]);
        $display("        This indicates a D-cache FLUSH/WRITE-BACK failure");
        $display("        The eviction did NOT write the dirty line to SDRAM");
        $display("");
        $display("        Debugging hints:");
        $display("        - Check DCache2Way dirty bit tracking");
        $display("        - Check write-back state machine in DCache2Way");
        $display("        - Check CacheArbiter write path");
        $display("        - Check PipelinedMemArbiterExtend write handling");
        $fatal(1, "D-cache flush assertion failed");
    end
    $display("[ASSERT] Test 2 PASSED: D-cache flush mechanism working correctly");

    // -----------------------------------------------------------------------
    // Test 3: Read back evicted line (should re-fetch from SDRAM)
    // -----------------------------------------------------------------------
    $display("\n--- Test 3: Re-read evicted line ---");

    $display("\n[FLUSH] Step 3: Read 0x00300 after eviction (cache miss)");
    data_read(19'h00300, data, success);
    check(success && data == 16'hDEAD,
          $sformatf("Re-read after eviction sees 0x%04h (expected 0xDEAD)", data));

    if (!success || data != 16'hDEAD) begin
        $display("[FATAL] Test 3 FAILED: Re-read expected 0xDEAD, got 0x%04h", data);
        $display("        SDRAM has correct value (0x%04h)", memory[19'h00300]);
        $display("        This indicates a cache fill issue, not a flush issue");
        $fatal(1, "Cache re-fill after eviction failed");
    end
    $display("[ASSERT] Test 3 PASSED: Re-read after eviction working");

    // -----------------------------------------------------------------------
    // Test 4: Multiple eviction cycles
    // -----------------------------------------------------------------------
    $display("\n--- Test 4: Multiple eviction cycles ---");

    // Write different values to same addresses
    data_write(19'h00300, 16'hAAAA, 2'b11, success);
    check(success, "Second write to 0x00300");

    data_write(19'h01300, 16'hBBBB, 2'b11, success);
    check(success, "Second write to 0x01300");

    data_write(19'h02300, 16'hCCCC, 2'b11, success);
    check(success, "Second write to 0x02300 (triggers second eviction)");

    repeat(60) @(posedge clk);

    check(memory[19'h00300] == 16'hAAAA,
          $sformatf("Second eviction: SDRAM[00300] = 0x%04h", memory[19'h00300]));

    if (memory[19'h00300] != 16'hAAAA) begin
        $display("[FATAL] Test 4 FAILED: Multiple eviction cycle broken");
        $fatal(1, "Multiple eviction test failed");
    end
    $display("[ASSERT] Test 4 PASSED: Multiple eviction cycles working");

    // -----------------------------------------------------------------------
    // Summary
    // -----------------------------------------------------------------------
    $display("\n==================================================");
    $display("D-Cache Flush Test Summary:");
    $display("  Total checks : %0d", test_count);
    $display("  Pass         : %0d", pass_count);
    $display("  Fail         : %0d", fail_count);
    $display("==================================================");

    if (fail_count == 0) begin
        $display("DCACHE FLUSH-ONLY TEST PASSED");
        $display("");
        $display("If this test passes but harvard_smc_tb fails, the issue is:");
        $display("  - ICache invalidation");
        $display("  - Arbiter scheduling between I and D caches");
        $display("  - Coherence sideband signaling");
        $finish(0);
    end else begin
        $display("DCACHE FLUSH-ONLY TEST FAILED");
        $display("");
        $display("The D-cache flush mechanism itself is broken.");
        $display("Focus debugging on DCache2Way and arbiter write paths.");
        $fatal(1, "DCACHE FLUSH-ONLY TEST FAILED");
    end
end

// Timeout safety
initial begin
    #2000000;
    $display("ERROR: harvard_dcache_flush_tb timeout");
    $finish(2);
end

// Waveform dump
initial begin
    $dumpfile("harvard_dcache_flush_tb.vcd");
    $dumpvars(0, harvard_dcache_flush_tb);
end

endmodule
`default_nettype wire
