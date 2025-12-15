// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Harvard Cache System Testbench
// Comprehensive verification of I-cache, D-cache, and Harvard arbiter
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module harvard_cache_tb;

// Configurable cache size parameters
// Can be overridden via command line: +define+CACHE_LINES=32
// Small caches (8-32 lines) reveal replacement/flush bugs faster
`ifndef CACHE_LINES
    `define CACHE_LINES 512
`endif
parameter CACHE_LINES = `CACHE_LINES;

// Clock and reset
reg clk;
reg reset;
reg cache_enabled;

// Instruction bus (CPU side)
reg  [19:1] instr_m_addr;
wire [15:0] instr_m_data_in;
reg         instr_m_access;
wire        instr_m_ack;

// Data bus (CPU side)
reg  [19:1] data_m_addr;
wire [15:0] data_m_data_in;
reg  [15:0] data_m_data_out;
reg         data_m_access;
wire        data_m_ack;
reg         data_m_wr_en;
reg  [1:0]  data_m_bytesel;

// Memory bus (backend)
wire [19:1] mem_m_addr;
reg  [15:0] mem_m_data_in;
wire [15:0] mem_m_data_out;
wire        mem_m_access;
reg         mem_m_ack;
wire        mem_m_wr_en;
wire [1:0]  mem_m_bytesel;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
string test_name;

// Memory model
reg [15:0] memory [0:524287];  // 1MB memory space
integer mem_latency;
integer mem_delay_counter;

// DUT instantiation
HarvardCacheSystem #(
    .ICACHE_LINES(CACHE_LINES),
    .DCACHE_LINES(CACHE_LINES)
) dut (
    .clk                (clk),
    .reset              (reset),
    .cache_enabled      (cache_enabled),
    // Instruction bus
    .instr_m_addr       (instr_m_addr),
    .instr_m_data_in    (instr_m_data_in),
    .instr_m_access     (instr_m_access),
    .instr_m_ack        (instr_m_ack),
    // Data bus
    .data_m_addr        (data_m_addr),
    .data_m_data_in     (data_m_data_in),
    .data_m_data_out    (data_m_data_out),
    .data_m_access      (data_m_access),
    .data_m_ack         (data_m_ack),
    .data_m_wr_en       (data_m_wr_en),
    .data_m_bytesel     (data_m_bytesel),
    // Memory interface
    .mem_m_addr         (mem_m_addr),
    .mem_m_data_in      (mem_m_data_in),
    .mem_m_data_out     (mem_m_data_out),
    .mem_m_access       (mem_m_access),
    .mem_m_ack          (mem_m_ack),
    .mem_m_wr_en        (mem_m_wr_en),
    .mem_m_bytesel      (mem_m_bytesel)
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 20ns period = 50 MHz
end

// Memory model with configurable latency
always @(posedge clk) begin
    if (reset) begin
        mem_m_ack <= 1'b0;
        mem_delay_counter <= 0;
    end else if (mem_m_access && !mem_m_ack) begin
        if (mem_delay_counter < mem_latency) begin
            mem_delay_counter <= mem_delay_counter + 1;
            mem_m_ack <= 1'b0;
        end else begin
            mem_m_ack <= 1'b1;
            if (mem_m_wr_en) begin
                // Write to memory
                if (mem_m_bytesel[0])
                    memory[mem_m_addr][7:0] <= mem_m_data_out[7:0];
                if (mem_m_bytesel[1])
                    memory[mem_m_addr][15:8] <= mem_m_data_out[15:8];
            end else begin
                // Read from memory
                mem_m_data_in <= memory[mem_m_addr];
            end
        end
    end else begin
        mem_m_ack <= 1'b0;
        mem_delay_counter <= 0;
    end
end

//=======================================================================
// Helper Tasks
//=======================================================================

// Instruction fetch
task instr_fetch(input [19:1] addr, output [15:0] data, output success);
    integer timeout;
begin
    timeout = 0;
    instr_m_addr = addr;
    instr_m_access = 1'b1;
    $display("  [DEBUG] instr_fetch: addr=0x%05h, access=1", addr);
    $display("  [DEBUG]   Before clk: ack=%b, data=0x%04h",
             instr_m_ack, instr_m_data_in);
    @(posedge clk);
    $display("  [DEBUG]   After 1st clk: ack=%b, data=0x%04h",
             instr_m_ack, instr_m_data_in);
    // Note: Internal signal access removed for 2-way cache compatibility
    // $display("  [DEBUG]     fetch_addr=0x%05h [3:1]=%0d, line_valid[%0d]=%b, filling_current=%b",
    //          dut.icache.fetch_address, dut.icache.fetch_address[3:1],
    //          dut.icache.fetch_address[3:1], dut.icache.line_valid[dut.icache.fetch_address[3:1]],
    //          dut.icache.filling_current);

    while (!instr_m_ack && timeout < 200) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (instr_m_ack) begin
        data = instr_m_data_in;
        success = 1'b1;
        $display("  [DEBUG]   GOT ACK after %0d cycles, data=0x%04h", timeout, data);
    end else begin
        data = 16'hXXXX;
        success = 1'b0;
        $display("ERROR: Instruction fetch timeout at address %h", addr);
    end

    instr_m_access = 1'b0;
    @(posedge clk);
end
endtask

// Data read
task data_read(input [19:1] addr, output [15:0] data, output success);
    integer timeout;
begin
    timeout = 0;
    data_m_addr = addr;
    data_m_wr_en = 1'b0;
    data_m_bytesel = 2'b11;
    data_m_access = 1'b1;
    $display("  [DEBUG] data_read: addr=0x%05h, access=1", addr);
    $display("  [DEBUG]   Before clk: ack=%b, data=0x%04h",
             data_m_ack, data_m_data_in);
    @(posedge clk);
    $display("  [DEBUG]   After 1st clk: ack=%b, data=0x%04h",
             data_m_ack, data_m_data_in);
    // Note: Internal signal access removed for 2-way cache compatibility
    // $display("  [DEBUG]     fetch_addr=0x%05h [3:1]=%0d, line_valid[%0d]=%b, filling_current=%b, updating=%b, flushing=%b",
    //          dut.dcache.fetch_address, dut.dcache.fetch_address[3:1],
    //          dut.dcache.fetch_address[3:1], dut.dcache.line_valid[dut.dcache.fetch_address[3:1]],
    //          dut.dcache.filling_current, dut.dcache.updating, dut.dcache.flushing);
    // $display("  [DEBUG]     do_fill=%b, do_flush=%b, dirty=%b",
    //          dut.dcache.do_fill, dut.dcache.do_flush, dut.dcache.dirty);

    while (!data_m_ack && timeout < 200) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (data_m_ack) begin
        data = data_m_data_in;
        success = 1'b1;
        $display("  [DEBUG] data_read: GOT ACK after %0d cycles, data=0x%04h", timeout, data);
    end else begin
        data = 16'hXXXX;
        success = 1'b0;
        $display("ERROR: Data read timeout at address %h", addr);
    end

    data_m_access = 1'b0;
    @(posedge clk);
end
endtask

// Data write
task data_write(input [19:1] addr, input [15:0] data, input [1:0] bytesel, output success);
    integer timeout;
begin
    timeout = 0;
    data_m_addr = addr;
    data_m_data_out = data;
    data_m_wr_en = 1'b1;
    data_m_bytesel = bytesel;
    data_m_access = 1'b1;
    $display("  [DEBUG] data_write: addr=0x%05h, data=0x%04h, bytesel=%b, wr_en=1", addr, data, bytesel);
    $display("  [DEBUG]   Before clk: ack=%b",
             data_m_ack);
    @(posedge clk);
    $display("  [DEBUG]   After 1st clk: ack=%b",
             data_m_ack);
    // Note: Internal signal access removed for 2-way cache compatibility
    // $display("  [DEBUG]     updating=%b, flushing=%b, accessing=%b, do_fill=%b, do_flush=%b, dirty=%b",
    //          dut.dcache.updating, dut.dcache.flushing, dut.dcache.accessing,
    //          dut.dcache.do_fill, dut.dcache.do_flush, dut.dcache.dirty);

    while (!data_m_ack && timeout < 200) begin
        @(posedge clk);
        timeout = timeout + 1;
        if (timeout % 10 == 0) begin
            $display("  [DEBUG]   Cycle %0d: ack=%b",
                     timeout, data_m_ack);
            // Note: Internal signal access removed for 2-way cache compatibility
            // $display("  [DEBUG]   Cycle %0d: ack=%b, busy=%b, dcache.m_access=%b, icache.m_access=%b, arb.state=%0d, arb.m_access=%b, m_ack=%b",
            //          timeout, data_m_ack, dut.dcache.busy,
            //          dut.dcache.m_access, dut.icache.m_access,
            //          dut.harvard_arbiter.state, dut.mem_m_access, dut.mem_m_ack);
        end
    end

    success = data_m_ack;
    if (success)
        $display("  [DEBUG] data_write: GOT ACK after %0d cycles", timeout);
    else
        $display("ERROR: Data write timeout at address %h", addr);

    data_m_access = 1'b0;
    data_m_wr_en = 1'b0;
    @(posedge clk);
end
endtask

// Initialize memory with test pattern
task init_memory();
    integer i;
begin
    for (i = 0; i < 524288; i = i + 1) begin
        memory[i] = i[15:0] ^ 16'hA5A5;  // Test pattern
    end
    $display("Memory initialized with test pattern");
end
endtask

// Check test result
task check_result(input condition, input string description);
begin
    test_count = test_count + 1;
    if (condition) begin
        pass_count = pass_count + 1;
        $display("[PASS] Test %0d: %s", test_count, description);
    end else begin
        fail_count = fail_count + 1;
        $display("[FAIL] Test %0d: %s", test_count, description);
    end
end
endtask

//=======================================================================
// Test Cases
//=======================================================================

initial begin
    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    reset = 1;
    cache_enabled = 1;
    instr_m_addr = 19'h0;
    instr_m_access = 0;
    data_m_addr = 19'h0;
    data_m_access = 0;
    data_m_wr_en = 0;
    data_m_bytesel = 2'b11;
    data_m_data_out = 16'h0;
    mem_latency = 2;  // 2 cycle memory latency

    $display("========================================");
    $display("Harvard Cache System Testbench");
    $display("Cache Configuration: LINES = %0d", CACHE_LINES);
    $display("========================================");

    // Initialize memory
    init_memory();

    // Release reset
    #100;
    reset = 0;
    #40;

    //==================================================================
    // Test 1: Basic I-cache Operation
    //==================================================================
    test_name = "Basic I-cache fetch";
    $display("\n--- Test 1: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;

        instr_fetch(19'h00100, data, success);
        check_result(success && data == (16'h0100 ^ 16'hA5A5),
                    "I-cache first fetch (miss->fill)");

        // Second fetch from same cache line (should hit)
        instr_fetch(19'h00101, data, success);
        check_result(success && data == (16'h0101 ^ 16'hA5A5),
                    "I-cache second fetch (hit)");
    end

    //==================================================================
    // Test 2: Basic D-cache Operation
    //==================================================================
    test_name = "Basic D-cache read/write";
    $display("\n--- Test 2: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;

        // Read from D-cache (miss)
        data_read(19'h00200, data, success);
        check_result(success && data == (16'h0200 ^ 16'hA5A5),
                    "D-cache read (miss->fill)");

        // Write to D-cache
        data_write(19'h00200, 16'h1234, 2'b11, success);
        check_result(success, "D-cache write");

        // Read back written data
        data_read(19'h00200, data, success);
        check_result(success && data == 16'h1234,
                    "D-cache read after write (verify)");
    end

    //==================================================================
    // Test 3: Parallel I-cache and D-cache Access
    //==================================================================
    test_name = "Parallel I-fetch and D-read";
    $display("\n--- Test 3: %s ---", test_name);
    begin
        reg [15:0] idata, ddata;
        reg isuccess, dsuccess;
        integer i;

        // Sequential access baseline
        for (i = 0; i < 8; i = i + 1) begin
            instr_fetch(19'h01000 + i, idata, isuccess);
            data_read(19'h02000 + i, ddata, dsuccess);
        end
        check_result(isuccess && dsuccess,
                    "Sequential I-fetch and D-read pattern");
    end

    //==================================================================
    // Test 4: Cache Line Fill Behavior
    //==================================================================
    test_name = "Cache line fill (8 words)";
    $display("\n--- Test 4: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;
        integer i;

        // Access 8 sequential addresses (one cache line)
        for (i = 0; i < 8; i = i + 1) begin
            instr_fetch(19'h03000 + i, data, success);
            check_result(success, $sformatf("I-cache line fill word %0d", i));
        end
    end

    //==================================================================
    // Test 5: D-cache Write-Through and Dirty Tracking
    //==================================================================
    test_name = "D-cache dirty line replacement";
    $display("\n--- Test 5: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;

        // For 2-way set-associative cache with 256 sets:
        // - Index = addr[11:4] (8 bits)
        // - Tag = addr[19:12] (8 bits)
        // - Line offset = addr[3:1] (3 bits)
        //
        // To trigger eviction, we need THREE accesses to same set:
        // 1. First write fills way 0
        // 2. Second access fills way 1
        // 3. Third access evicts LRU (way 0 with our write)
        //
        // Addresses mapping to same set (index 0):
        //   0x04000, 0x05000, 0x06000, 0x07000, etc.
        //   All have addr[11:4] = 0x00

        // Write to create dirty line (fills way 0 of set 0)
        data_write(19'h04000, 16'hBEEF, 2'b11, success);
        check_result(success, "Create dirty line in D-cache");

        // Access another address in same set (fills way 1 of set 0)
        data_read(19'h05000, data, success);
        check_result(success, "Fill second way of set");

        // Access a THIRD address in same set - this triggers eviction!
        data_read(19'h06000, data, success);
        check_result(success, "Trigger D-cache line replacement");

        // Allow time for victim writeback to complete
        repeat (20) @(posedge clk);

        // Verify original write was flushed to memory
        check_result(memory[19'h04000] == 16'hBEEF,
                    "Dirty line flushed to memory");
    end

    //==================================================================
    // Test 6: Byte-Level Writes
    //==================================================================
    test_name = "D-cache byte-level writes";
    $display("\n--- Test 6: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;

        // Initialize location
        data_write(19'h05000, 16'h0000, 2'b11, success);

        // Write low byte only
        data_write(19'h05000, 16'h00AB, 2'b01, success);
        data_read(19'h05000, data, success);
        check_result(success && data[7:0] == 8'hAB,
                    "Byte write (low byte)");

        // Write high byte only
        data_write(19'h05000, 16'hCD00, 2'b10, success);
        data_read(19'h05000, data, success);
        check_result(success && data == 16'hCDAB,
                    "Byte write (high byte)");
    end

    //==================================================================
    // Test 7: Cache Disabled Operation
    //==================================================================
    test_name = "Cache disabled bypass mode";
    $display("\n--- Test 7: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;

        cache_enabled = 0;
        #20;

        // Access should bypass cache
        instr_fetch(19'h06000, data, success);
        check_result(success, "I-fetch with cache disabled");

        data_read(19'h06100, data, success);
        check_result(success, "D-read with cache disabled");

        cache_enabled = 1;
        #20;
    end

    //==================================================================
    // Test 8: Stress Test - Mixed Access Pattern
    //==================================================================
    test_name = "Stress test - mixed I/D access";
    $display("\n--- Test 8: %s ---", test_name);
    begin
        reg [15:0] idata, ddata;
        reg isuccess, dsuccess;
        integer i;
        integer errors;

        errors = 0;
        for (i = 0; i < 100; i = i + 1) begin
            instr_fetch(19'h10000 + (i * 3), idata, isuccess);
            data_read(19'h20000 + (i * 5), ddata, dsuccess);
            if (!isuccess || !dsuccess) errors = errors + 1;

            if (i[1:0] == 0) begin
                data_write(19'h20000 + (i * 5), i[15:0], 2'b11, dsuccess);
                if (!dsuccess) errors = errors + 1;
            end
        end
        check_result(errors == 0,
                    $sformatf("Stress test completed (%0d errors)", errors));
    end

    //==================================================================
    // Test 9: Sequential Access Performance
    //==================================================================
    test_name = "Sequential access performance";
    $display("\n--- Test 9: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;
        integer i;
        integer start_time, end_time;

        start_time = $time;
        for (i = 0; i < 64; i = i + 1) begin
            instr_fetch(19'h30000 + i, data, success);
        end
        end_time = $time;

        $display("Sequential I-fetch: 64 words in %0d ns", end_time - start_time);
        check_result(success, "Sequential access completed");
    end

    //==================================================================
    // Test 10: Cache Coherency
    //==================================================================
    test_name = "Cache coherency test";
    $display("\n--- Test 10: %s ---", test_name);
    begin
        reg [15:0] data;
        reg success;

        // Write through D-cache (fills way 0 of its set)
        data_write(19'h40000, 16'hCAFE, 2'b11, success);

        // For 2-way cache, need to fill both ways then access a third
        // to trigger eviction. Use addresses in same set.
        // 0x40000, 0x41000, 0x42000 all map to same set (index = addr[11:4])
        data_read(19'h41000, data, success);  // Fill way 1
        data_read(19'h42000, data, success);  // Evict LRU (0x40000)
        repeat (20) @(posedge clk);  // Allow victim writeback

        // Read original address - should get correct value
        data_read(19'h40000, data, success);
        check_result(success && data == 16'hCAFE,
                    "D-cache coherency after replacement");
    end

    //==================================================================
    // Final Results
    //==================================================================
    #1000;

    $display("\n========================================");
    $display("Test Results:");
    $display("  Total: %0d", test_count);
    $display("  Pass:  %0d", pass_count);
    $display("  Fail:  %0d", fail_count);
    $display("========================================");

    if (fail_count == 0) begin
        $display("*** ALL TESTS PASSED ***");
        $finish(0);
    end else begin
        $display("*** SOME TESTS FAILED ***");
        $finish(1);
    end
end

// Timeout watchdog
initial begin
    #1000000;  // 1ms timeout
    $display("\n========================================");
    $display("ERROR: Simulation timeout!");
    $display("========================================");
    $finish(2);
end

// Waveform dump for debugging
initial begin
    $dumpfile("harvard_cache_tb.vcd");
    $dumpvars(0, harvard_cache_tb);
end

endmodule
`default_nettype wire
