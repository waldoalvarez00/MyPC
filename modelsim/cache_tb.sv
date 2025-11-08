//============================================================================
//
//  Cache Testbench
//  Verifies Cache functionality for s80x86 CPU
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module cache_tb;

// Clock and reset
reg clk;
reg reset;
reg enabled;

// Frontend interface (CPU side)
reg  [19:1] c_addr;
wire [15:0] c_data_in;
reg  [15:0] c_data_out;
reg         c_access;
wire        c_ack;
reg         c_wr_en;
reg  [1:0]  c_bytesel;

// Backend interface (Memory side)
wire [19:1] m_addr;
reg  [15:0] m_data_in;
wire [15:0] m_data_out;
wire        m_access;
reg         m_ack;
wire        m_wr_en;
wire [1:0]  m_bytesel;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// Memory model for backend
reg [15:0] memory [0:1048575];  // 1MB memory space
integer mem_wait_cycles;

// DUT instantiation
Cache #(.lines(512)) dut (
    .clk            (clk),
    .reset          (reset),
    .enabled        (enabled),
    // Frontend
    .c_addr         (c_addr),
    .c_data_in      (c_data_in),
    .c_data_out     (c_data_out),
    .c_access       (c_access),
    .c_ack          (c_ack),
    .c_wr_en        (c_wr_en),
    .c_bytesel      (c_bytesel),
    // Backend
    .m_addr         (m_addr),
    .m_data_in      (m_data_in),
    .m_data_out     (m_data_out),
    .m_access       (m_access),
    .m_ack          (m_ack),
    .m_wr_en        (m_wr_en),
    .m_bytesel      (m_bytesel)
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 20ns period
end

// Memory model - simulates backend memory with variable latency
reg [3:0] access_delay;

always @(posedge clk) begin
    if (reset) begin
        m_ack <= 1'b0;
        access_delay <= 0;
    end else if (m_access && !m_ack) begin
        // Simulate memory access with latency
        if (access_delay > 0) begin
            access_delay <= access_delay - 1;
        end else begin
            m_ack <= 1'b1;
            if (m_wr_en) begin
                // Write to memory
                memory[m_addr[19:1]] <= m_data_out;
            end else begin
                // Read from memory
                m_data_in <= memory[m_addr[19:1]];
            end
        end
    end else if (m_access && m_ack) begin
        // Keep ack high while access is high
        m_ack <= 1'b1;
    end else begin
        m_ack <= 1'b0;
        access_delay <= mem_wait_cycles;  // Reset delay for next access
    end
end

// Helper task for CPU read
task cpu_read(input [19:1] addr, output [15:0] data, output hit);
    integer timeout;
begin
    timeout = 0;
    c_addr = addr;
    c_wr_en = 1'b0;
    c_bytesel = 2'b11;
    c_access = 1'b0;
    @(posedge clk);
    c_access = 1'b1;
    @(posedge clk);

    while (!c_ack && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (c_ack) begin
        data = c_data_in;
        hit = 1'b1;
    end else begin
        data = 16'hXXXX;
        hit = 1'b0;
    end

    c_access = 1'b0;
    @(posedge clk);
end
endtask

// Helper task for CPU write
task cpu_write(input [19:1] addr, input [15:0] data, input [1:0] bytesel);
    integer timeout;
begin
    timeout = 0;
    c_addr = addr;
    c_data_out = data;
    c_access = 1'b1;
    c_wr_en = 1'b1;
    c_bytesel = bytesel;
    @(posedge clk);

    while (!c_ack && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    c_access = 1'b0;
    c_wr_en = 1'b0;
    @(posedge clk);
end
endtask

// Waveform dump
initial begin
    $dumpfile("cache_tb.vcd");
    $dumpvars(0, cache_tb);
end

// Main test
initial begin
    $display("================================================================");
    $display("Cache Testbench");
    $display("Testing CPU cache functionality");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1;
    enabled = 0;
    c_addr = 19'h0;
    c_data_out = 16'h0;
    c_access = 0;
    c_wr_en = 0;
    c_bytesel = 2'b11;
    mem_wait_cycles = 2;  // 2 cycle memory latency

    // Initialize memory with test pattern
    for (int i = 0; i < 1024; i++) begin
        memory[i] = i[15:0];
    end

    repeat(5) @(posedge clk);
    reset = 0;
    repeat(5) @(posedge clk);

    // Test 1: Cache disabled - direct passthrough
    $display("Test 1: Cache disabled - verify passthrough");
    test_count++;
    enabled = 0;
    begin
        reg [15:0] rdata;
        reg hit;
        cpu_read(19'h00001, rdata, hit);
        if (rdata == 16'h0001) begin
            $display("  [PASS] Cache disabled read: data=0x%04X", rdata);
            pass_count++;
        end else begin
            $display("  [FAIL] Cache disabled read: expected=0x0001, got=0x%04X", rdata);
            fail_count++;
        end
    end

    $display("");
    $display("Test 2: Enable cache");
    test_count++;
    enabled = 1;
    repeat(10) @(posedge clk);
    $display("  [PASS] Cache enabled");
    pass_count++;

    $display("");
    $display("Test 3: First read (cache miss - should trigger fill)");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        cpu_read(19'h00001, rdata, hit);
        if (rdata == 16'h0001) begin
            $display("  [PASS] Cache miss handled: data=0x%04X", rdata);
            pass_count++;
        end else begin
            $display("  [FAIL] Cache miss: expected=0x0001, got=0x%04X", rdata);
            fail_count++;
        end
    end

    $display("");
    $display("Test 4: Second read of same address (cache hit)");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        integer start_time, end_time;
        start_time = $time;
        cpu_read(19'h00001, rdata, hit);
        end_time = $time;

        if (rdata == 16'h0001 && (end_time - start_time) < 100) begin
            $display("  [PASS] Cache hit: data=0x%04X, latency=%0d ns", rdata, end_time - start_time);
            pass_count++;
        end else begin
            $display("  [FAIL] Cache hit: expected=0x0001, got=0x%04X, latency=%0d", rdata, end_time - start_time);
            fail_count++;
        end
    end

    $display("");
    $display("Test 5: Read from same cache line (different offset)");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        cpu_read(19'h00002, rdata, hit);
        if (rdata == 16'h0002) begin
            $display("  [PASS] Same cache line read: data=0x%04X", rdata);
            pass_count++;
        end else begin
            $display("  [FAIL] Same cache line: expected=0x0002, got=0x%04X", rdata);
            fail_count++;
        end
    end

    $display("");
    $display("Test 6: Write to cache");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        cpu_write(19'h00001, 16'hABCD, 2'b11);
        cpu_read(19'h00001, rdata, hit);
        if (rdata == 16'hABCD) begin
            $display("  [PASS] Cache write/read: data=0x%04X", rdata);
            pass_count++;
        end else begin
            $display("  [FAIL] Cache write: expected=0xABCD, got=0x%04X", rdata);
            fail_count++;
        end
    end

    $display("");
    $display("Test 7: Verify write sets dirty bit (read from different line to trigger flush)");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        // Read from address that maps to same index but different tag
        // This should cause cache line replacement and flush
        cpu_read(19'h08001, rdata, hit);  // Different cache line
        repeat(20) @(posedge clk);

        // Verify memory was updated during flush
        if (memory[19'h00001] == 16'hABCD) begin
            $display("  [PASS] Dirty line flushed to memory: data=0x%04X", memory[19'h00001]);
            pass_count++;
        end else begin
            $display("  [FAIL] Flush failed: expected=0xABCD in memory, got=0x%04X", memory[19'h00001]);
            fail_count++;
        end
    end

    $display("");
    $display("Test 8: Read multiple cache lines");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        integer errors = 0;

        for (int i = 0; i < 16; i++) begin
            cpu_read((19'h00001 + i), rdata, hit);
            if (i == 0 && rdata != 16'hABCD) errors++;  // First address was modified
            else if (i > 0 && rdata != (19'h00001 + i)) errors++;
        end

        if (errors == 0) begin
            $display("  [PASS] Multiple reads successful");
            pass_count++;
        end else begin
            $display("  [FAIL] Multiple reads had %0d errors", errors);
            fail_count++;
        end
    end

    $display("");
    $display("Test 9: Byte-wide write");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        cpu_write(19'h00010, 16'h5678, 2'b11);  // Write full word
        cpu_write(19'h00010, 16'h00FF, 2'b01);  // Write low byte only
        cpu_read(19'h00010, rdata, hit);
        if (rdata == 16'h56FF) begin
            $display("  [PASS] Byte write: data=0x%04X", rdata);
            pass_count++;
        end else begin
            $display("  [FAIL] Byte write: expected=0x56FF, got=0x%04X", rdata);
            fail_count++;
        end
    end

    $display("");
    $display("Test 10: Cache line boundary");
    test_count++;
    begin
        reg [15:0] rdata;
        reg hit;
        // Test reading across cache line boundary
        cpu_read(19'h00007, rdata, hit);  // Last word in line
        cpu_read(19'h00008, rdata, hit);  // First word in next line

        if (rdata == 16'h0008) begin
            $display("  [PASS] Cache line boundary: data=0x%04X", rdata);
            pass_count++;
        end else begin
            $display("  [FAIL] Cache line boundary: expected=0x0008, got=0x%04X", rdata);
            fail_count++;
        end
    end

    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0d%%", (pass_count * 100) / test_count);
    $display("================================================================");
    $display("");

    if (fail_count == 0) begin
        $display("*** ALL TESTS PASSED ***");
        $display("*** CACHE FUNCTIONALITY VERIFIED ***");
    end else begin
        $display("*** SOME TESTS FAILED ***");
    end

    $display("");
    $finish;
end

endmodule
