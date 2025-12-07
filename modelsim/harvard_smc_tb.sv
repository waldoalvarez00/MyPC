// Harvard I/D Cache Self-Modifying Code Testbench
// ------------------------------------------------
// This testbench exercises the new D→I invalidation path by:
//   1. Fetching an instruction via ICache2Way (through CacheArbiter and
//      PipelinedMemArbiterExtend to SDRAM).
//   2. Modifying the same address via DCache2Way (write-back).
//   3. Forcing a dirty-line flush in DCache2Way so the new value reaches SDRAM.
//   4. Verifying that a subsequent instruction fetch sees the updated value,
//      i.e., ICache2Way invalidation + refetch work correctly.

`timescale 1ns/1ps
`default_nettype none

module harvard_smc_tb;

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

// CPU instruction interface
logic [19:1] instr_addr;
logic [15:0] instr_data_in;
logic        instr_access;
logic        instr_ack;

// CPU data interface
logic [19:1] data_addr;
logic [15:0] data_data_in;
logic [15:0] data_data_out;
logic        data_access;
logic        data_ack;
logic        data_wr_en;
logic [1:0]  data_bytesel;

// I-Cache backend
logic [19:1] ic_m_addr;
logic [15:0] ic_m_data_in;
logic        ic_m_access;
logic        ic_m_ack;

// D-Cache backend - main port
logic [19:1] dc_m_addr;
logic [15:0] dc_m_data_in;
logic [15:0] dc_m_data_out;
logic        dc_m_access;
logic        dc_m_ack;
logic        dc_m_wr_en;
logic [1:0]  dc_m_bytesel;

// D-Cache backend - victim writeback port (non-blocking)
logic [18:0] dc_vwb_addr;
logic [15:0] dc_vwb_data_out;
logic        dc_vwb_access;
logic        dc_vwb_ack;
logic        dc_vwb_wr_en;
logic [1:0]  dc_vwb_bytesel;

// Unified cache -> memory bus (CacheArbiter)
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

// I-cache invalidation tap from PipelinedMemArbiterExtend
logic        icache_inval_valid;
logic [19:1] icache_inval_addr;

// D↔I cache coherence sideband
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
// DUT Instances
// ---------------------------------------------------------------------------

// Instruction cache: 2-way set associative
ICache2Way #(.sets(SETS)) ICacheInst (
    .clk(clk),
    .reset(reset),
    .enabled(1'b1),
    // CPU side
    .c_addr(instr_addr),
    .c_data_in(instr_data_in),
    .c_access(instr_access),
    .c_ack(instr_ack),
    // Memory side
    .m_addr(ic_m_addr),
    .m_data_in(ic_m_data_in),
    .m_access(ic_m_access),
    .m_ack(ic_m_ack),
    // Coherence invalidation from final arbiter
    .inval_valid(icache_inval_valid),
    .inval_addr(icache_inval_addr),
    // D-cache coherence sideband
    .coh_wr_valid(coh_wr_valid),
    .coh_wr_addr(coh_wr_addr),
    .coh_wr_data(coh_wr_data),
    .coh_wr_bytesel(coh_wr_bytesel),
    .coh_probe_valid(coh_probe_valid),
    .coh_probe_addr(coh_probe_addr),
    .coh_probe_present(coh_probe_present)
);

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
    // Memory side - victim writeback port (non-blocking)
    .vwb_addr(dc_vwb_addr),
    .vwb_data_out(dc_vwb_data_out),
    .vwb_access(dc_vwb_access),
    .vwb_ack(dc_vwb_ack),
    .vwb_wr_en(dc_vwb_wr_en),
    .vwb_bytesel(dc_vwb_bytesel),
    // Coherence sideband
    .coh_wr_valid(coh_wr_valid),
    .coh_wr_addr(coh_wr_addr),
    .coh_wr_data(coh_wr_data),
    .coh_wr_bytesel(coh_wr_bytesel),
    .coh_probe_valid(coh_probe_valid),
    .coh_probe_addr(coh_probe_addr),
    .coh_probe_present(coh_probe_present)
);

// 3-Way cache arbiter: I-cache, D-cache main, D-cache victim writeback
HarvardArbiter3Way CacheArb (
    .clk(clk),
    .reset(reset),
    // I-cache interface (read-only)
    .icache_m_addr(ic_m_addr),
    .icache_m_data_in(ic_m_data_in),
    .icache_m_access(ic_m_access),
    .icache_m_ack(ic_m_ack),
    // D-cache main interface (read/write for fills and flushes)
    .dcache_m_addr(dc_m_addr),
    .dcache_m_data_in(dc_m_data_in),
    .dcache_m_data_out(dc_m_data_out),
    .dcache_m_access(dc_m_access),
    .dcache_m_ack(dc_m_ack),
    .dcache_m_wr_en(dc_m_wr_en),
    .dcache_m_bytesel(dc_m_bytesel),
    // D-cache victim writeback interface (write-only, non-blocking)
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

// Final SDRAM arbiter with I-cache invalidation
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
    // VGA priority hint disabled (round-robin)
    .vga_active_display(1'b0),
    // I-cache invalidation tap
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

// Instruction fetch via I-cache
task automatic instr_fetch(input [19:1] addr,
                           output [15:0] data,
                           output bit success);
    integer timeout;
begin
    instr_addr   = addr;
    instr_access = 1'b1;
    success      = 1'b0;
    timeout      = 0;

    @(posedge clk);
    while (!instr_ack && timeout < 200) begin
        @(posedge clk);
        timeout++;
    end

    if (instr_ack) begin
        data    = instr_data_in;
        success = 1'b1;
    end

    instr_access = 1'b0;
    @(posedge clk);
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

// Data read via D-cache (used to exercise LRU like dcache2way_tb)
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
// Test sequence: self-modifying code via D-cache write-back + invalidation
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

    // Specific code locations used for this test map to the same D-cache set:
    //  - 0x00300 : target instruction to modify
    //  - 0x01300, 0x02300 : additional lines in same set to force eviction
    memory[19'h00300] = 16'h1111;  // Original instruction word
    memory[19'h01300] = 16'h2222;
    memory[19'h02300] = 16'h3333;

    // Reset
    reset        = 1'b1;
    instr_addr   = 19'h0;
    instr_access = 1'b0;
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
    $display("Harvard Cache Self-Modifying Code Test");
    $display("ICache2Way + DCache2Way + CacheArbiter + PipelinedMemArbiterExtend");
    $display("Cache Configuration: SETS = %0d", SETS);
    $display("==================================================");

    // 1) Initial I-fetch should see original code (1111)
    $display("\n[SMC] Step 1: Initial instruction fetch at 0x00300");
    instr_fetch(19'h00300, data, success);
    check(success && data == 16'h1111,
          $sformatf("Initial I-fetch returns original code (got 0x%04h)", data));

    // 2) Modify code via D-cache (write-back, not yet visible in memory)
    $display("\n[SMC] Step 2: Data write new code (0xDEAD) at 0x00300 via D-cache");
    data_write(19'h00300, 16'hDEAD, 2'b11, success);
    check(success, "D-cache write of new code completed");

    // Read back through D-cache to mirror dcache2way_tb LRU behavior and
    // confirm the cache now holds the updated value before forcing eviction.
    $display("\n[SMC] Step 2b: Data read back at 0x00300 via D-cache");
    data_read(19'h00300, data, success);
    check(success && data == 16'hDEAD,
          $sformatf("D-cache readback sees updated code (0x%04h)", data));

    // CRITICAL ASSERTION: D-cache must return the written value before eviction
    // This isolates D-cache write/read issues from flush/invalidation issues
    if (!success || data != 16'hDEAD) begin
        $display("[FATAL] Step 2b FAILED: D-cache readback expected 0xDEAD, got 0x%04h", data);
        $display("        This indicates a D-cache write/read issue, NOT a flush problem");
        $display("        SDRAM still has: 0x%04h (write-back deferred is OK)", memory[19'h00300]);
        $fatal(1, "D-cache readback assertion failed - stopping test");
    end
    $display("[ASSERT] Step 2b PASSED: D-cache correctly returns 0xDEAD");
    $display("         Note: SDRAM may still have 0x%04h (write-back deferred)", memory[19'h00300]);

    // 3) Force D-cache dirty line flush by writing two more lines in same set
    //    (pattern reused from dcache2way_tb.sv Test 5: Dirty Line Flush)
    $display("\n[SMC] Step 3: Forcing D-cache dirty line flush for 0x00300");
    data_write(19'h01300, 16'hBEEF, 2'b11, success);
    check(success, "D-cache write at 0x01300 (same set)");
    data_write(19'h02300, 16'hCAFE, 2'b11, success);
    check(success, "D-cache write at 0x02300 (same set, triggers eviction)");

    // Allow time for write-back + invalidation pipeline to complete
    repeat(60) @(posedge clk);

    // At this point, DCache2Way should have flushed the dirty line for 0x00300
    // to SDRAM, and PipelinedMemArbiterExtend should have raised an invalidate
    // event so ICache2Way drops any stale copy.
    check(memory[19'h00300] == 16'hDEAD,
          $sformatf("SDRAM holds updated code at 0x00300 (0x%04h)", memory[19'h00300]));

    // CRITICAL ASSERTION: SDRAM must have the flushed value after eviction
    // This isolates D-cache flush issues from I-cache invalidation issues
    if (memory[19'h00300] != 16'hDEAD) begin
        $display("[FATAL] Step 3 FAILED: SDRAM at 0x00300 expected 0xDEAD, got 0x%04h", memory[19'h00300]);
        $display("        This indicates a D-cache FLUSH issue");
        $display("        The dirty line was NOT written back to SDRAM during eviction");
        $display("        Check: DCache2Way dirty tracking, write-back state machine, arbiter scheduling");
        $display("        Other SDRAM locations:");
        $display("          mem[01300] = 0x%04h (expected 0xBEEF)", memory[19'h01300]);
        $display("          mem[02300] = 0x%04h (expected 0xCAFE)", memory[19'h02300]);
        $fatal(1, "SDRAM eviction assertion failed - stopping test");
    end
    $display("[ASSERT] Step 3 PASSED: SDRAM correctly holds 0xDEAD after eviction");
    $display("         D-cache flush mechanism is working correctly");

    // 4) Re-fetch instruction and verify new code is observed
    $display("\n[SMC] Step 4: Re-fetch instruction at 0x00300 after modification");
    instr_fetch(19'h00300, data, success);
    check(success && data == 16'hDEAD,
          $sformatf("I-fetch after D-side modification returns updated code (0x%04h)", data));

    // Summary
    $display("\n==================================================");
    $display("SMC Test Summary:");
    $display("  Total checks : %0d", test_count);
    $display("  Pass         : %0d", pass_count);
    $display("  Fail         : %0d", fail_count);
    $display("==================================================");

    if (fail_count == 0) begin
        $display("✓✓✓ SELF-MODIFYING CODE TEST PASSED ✓✓✓");
        $finish(0);
    end else begin
        $display("✗✗✗ SELF-MODIFYING CODE TEST FAILED ✗✗✗");
        // Use $fatal to propagate a non-zero exit code to the wrapper script.
        $fatal(1, "SELF-MODIFYING CODE TEST FAILED");
    end
end

// Timeout safety
initial begin
    #2000000;
    $display("ERROR: harvard_smc_tb timeout");
    $finish(2);
end

// Waveform dump
initial begin
    $dumpfile("harvard_smc_tb.vcd");
    $dumpvars(0, harvard_smc_tb);
end

endmodule
`default_nettype wire
