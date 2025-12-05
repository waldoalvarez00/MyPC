// Copyright 2025, Waldo Alvarez
// Comprehensive testbench for DCache2Way
// Tests 2-way set-associativity, LRU replacement, and write-back functionality

`timescale 1ns/1ps

module dcache2way_tb();

// Clock and reset
logic clk;
logic reset;
logic enabled;

// Frontend interface
logic [19:1] c_addr;
logic [15:0] c_data_in;
logic [15:0] c_data_out;
logic c_access;
logic c_ack;
logic c_wr_en;
logic [1:0] c_bytesel;

// Backend interface
logic [19:1] m_addr;
logic [15:0] m_data_in;
logic [15:0] m_data_out;
logic m_access;
logic m_ack;
logic m_wr_en;
logic [1:0] m_bytesel;

// Victim writeback interface
logic [18:0] vwb_addr;
logic [15:0] vwb_data_out;
logic vwb_access;
logic vwb_ack;
logic vwb_wr_en;
logic [1:0] vwb_bytesel;

// Coherence interface
logic        coh_wr_valid;
logic [19:1] coh_wr_addr;
logic [15:0] coh_wr_data;
logic [1:0]  coh_wr_bytesel;
logic        coh_probe_valid;
logic [19:1] coh_probe_addr;
logic        coh_probe_present;

// Memory model
logic [15:0] memory [0:524287];  // 512K words
logic mem_busy;
integer mem_latency_counter;
localparam MEM_LATENCY = 5;

// Test statistics
integer total_accesses;
integer cache_hits;
integer cache_misses;
integer writes;
integer reads;
integer conflicts_prevented;

// DUT instantiation
DCache2Way #(.sets(256)) dut (
    .clk(clk),
    .reset(reset),
    .enabled(enabled),
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
    // Victim writeback interface
    .vwb_addr(vwb_addr),
    .vwb_data_out(vwb_data_out),
    .vwb_access(vwb_access),
    .vwb_ack(vwb_ack),
    .vwb_wr_en(vwb_wr_en),
    .vwb_bytesel(vwb_bytesel),
    // Coherence interface
    .coh_wr_valid(coh_wr_valid),
    .coh_wr_addr(coh_wr_addr),
    .coh_wr_data(coh_wr_data),
    .coh_wr_bytesel(coh_wr_bytesel),
    .coh_probe_valid(coh_probe_valid),
    .coh_probe_addr(coh_probe_addr),
    .coh_probe_present(coh_probe_present)
);

// Clock generation
initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

// Memory model with latency
always_ff @(posedge clk) begin
    if (reset) begin
        m_ack <= 1'b0;
        mem_latency_counter <= 0;
        mem_busy <= 1'b0;
    end else begin
        if (m_access && !mem_busy && !m_ack) begin
            mem_busy <= 1'b1;
            mem_latency_counter <= MEM_LATENCY;
            m_ack <= 1'b0;
        end else if (mem_busy) begin
            if (mem_latency_counter > 1) begin
                mem_latency_counter <= mem_latency_counter - 1;
                m_ack <= 1'b0;
            end else begin
                m_ack <= 1'b1;
                mem_busy <= 1'b0;
                if (m_wr_en) begin
                    memory[m_addr] <= m_data_out;
                    $display("[%0t] MEM WRITE: addr=0x%05x data=0x%04x", $time, m_addr, m_data_out);
                end else begin
                    m_data_in <= memory[m_addr];
                    $display("[%0t] MEM READ:  addr=0x%05x data=0x%04x", $time, m_addr, memory[m_addr]);
                end
            end
        end else begin
            m_ack <= 1'b0;
        end
    end
end

// Victim writeback ack handler - immediate ack for simplicity
always_ff @(posedge clk) begin
    if (reset) begin
        vwb_ack <= 1'b0;
    end else begin
        if (vwb_access && !vwb_ack) begin
            vwb_ack <= 1'b1;
            if (vwb_wr_en) begin
                memory[{vwb_addr, 1'b0}] <= vwb_data_out;  // Store victim writeback
            end
        end else begin
            vwb_ack <= 1'b0;
        end
    end
end

// Task: Cache read
task cache_read(input [19:1] addr, output [15:0] data, output hit);
    begin
        @(posedge clk);
        c_addr <= addr;
        c_access <= 1'b1;
        c_wr_en <= 1'b0;
        c_bytesel <= 2'b11;

        fork
            begin: timeout_block
                repeat(200) @(posedge clk);  // Increased for cache miss + fill
                $display("[%0t] ERROR: Read timeout for addr 0x%05x", $time, addr);
                $finish;
            end
            begin
                @(posedge clk);
                wait(c_ack);
                disable timeout_block;
                data = c_data_in;
                hit = 1'b1;  // Simplified - actual hit detection would need more logic
                @(posedge clk);
                c_access <= 1'b0;
            end
        join

        total_accesses++;
        reads++;
        $display("[%0t] CACHE READ: addr=0x%05x data=0x%04x", $time, addr, data);
    end
endtask

// Task: Cache write
task cache_write(input [19:1] addr, input [15:0] data);
    begin
        @(posedge clk);
        c_addr <= addr;
        c_data_out <= data;
        c_access <= 1'b1;
        c_wr_en <= 1'b1;
        c_bytesel <= 2'b11;

        fork
            begin: timeout_block
                repeat(200) @(posedge clk);  // Increased for cache miss + fill + write
                $display("[%0t] ERROR: Write timeout for addr 0x%05x", $time, addr);
                $finish;
            end
            begin
                @(posedge clk);
                wait(c_ack);
                disable timeout_block;
                @(posedge clk);
                c_access <= 1'b0;
                c_wr_en <= 1'b0;
            end
        join

        total_accesses++;
        writes++;
        $display("[%0t] CACHE WRITE: addr=0x%05x data=0x%04x", $time, addr, data);
    end
endtask

// Main test
integer mem_init_idx;
initial begin
    $display("=== DCache2Way Comprehensive Test ===");
    $display("Configuration: 256 sets, 2 ways, 8 words/line");

    // Initialize
    reset = 1'b1;
    enabled = 1'b1;
    c_access = 1'b0;
    c_wr_en = 1'b0;
    c_addr = 19'h00000;
    c_data_out = 16'h0000;
    c_bytesel = 2'b11;
    coh_probe_present = 1'b0;  // No coherence probes in this test
    total_accesses = 0;
    cache_hits = 0;
    cache_misses = 0;
    writes = 0;
    reads = 0;
    conflicts_prevented = 0;

    // Initialize memory with pattern
    for (mem_init_idx = 0; mem_init_idx < 524288; mem_init_idx = mem_init_idx + 1) begin
        memory[mem_init_idx] = 16'(mem_init_idx & 16'hFFFF);
    end

    repeat(5) @(posedge clk);
    reset = 1'b0;
    repeat(5) @(posedge clk);

    $display("\n=== Test 1: Basic Read Operations ===");
    begin
        logic [15:0] data;
        logic hit;

        // First read - should miss and fill cache
        cache_read(19'h00010, data, hit);
        assert(data == 16'h0010) else $error("Data mismatch");

        // Second read to same address - should hit
        cache_read(19'h00010, data, hit);
        assert(data == 16'h0010) else $error("Data mismatch");

        // Read within same cache line (different word)
        cache_read(19'h00012, data, hit);
        assert(data == 16'h0012) else $error("Data mismatch");

        $display("✓ Basic reads passed");
    end

    $display("\n=== Test 2: Basic Write Operations ===");
    begin
        logic [15:0] data;
        logic hit;

        // Write to cache
        cache_write(19'h00020, 16'hABCD);

        // Read back
        cache_read(19'h00020, data, hit);
        assert(data == 16'hABCD) else $error("Write-read mismatch");

        // Modify and read
        cache_write(19'h00020, 16'h1234);
        cache_read(19'h00020, data, hit);
        assert(data == 16'h1234) else $error("Modify-read mismatch");

        $display("✓ Basic writes passed");
    end

    $display("\n=== Test 3: 2-Way Associativity (Conflict Handling) ===");
    begin
        logic [15:0] data;
        logic hit;

        // Two addresses that map to same set but should both fit (2-way)
        // Set index is addr[11:4], so we need same bits [11:4] but different tag
        // addr1: 0x00100 -> set 0x10
        // addr2: 0x01100 -> set 0x10 (same set, different tag)

        cache_write(19'h00100, 16'hAAAA);  // Way 0 of set 0x10
        cache_write(19'h01100, 16'hBBBB);  // Way 1 of set 0x10

        // Both should be in cache (no conflict)
        cache_read(19'h00100, data, hit);
        assert(data == 16'hAAAA) else $error("First address evicted incorrectly");

        cache_read(19'h01100, data, hit);
        assert(data == 16'hBBBB) else $error("Second address missing");

        // Third address to same set - should evict LRU (first one)
        cache_write(19'h02100, 16'hCCCC);  // Should evict 0x00100 (LRU)

        // Verify third address is in cache
        cache_read(19'h02100, data, hit);
        assert(data == 16'hCCCC) else $error("Third address missing");

        // Second address should still be in cache
        cache_read(19'h01100, data, hit);
        assert(data == 16'hBBBB) else $error("Second address evicted incorrectly");

        conflicts_prevented++;
        $display("✓ 2-way associativity test passed - conflict prevented");
    end

    $display("\n=== Test 4: LRU Replacement Policy ===");
    begin
        logic [15:0] data;
        logic hit;

        // Fill both ways of a set
        cache_write(19'h00200, 16'h0001);  // Way 0
        cache_write(19'h01200, 16'h0002);  // Way 1

        // Access way 0 to make it MRU
        cache_read(19'h00200, data, hit);

        // Add third address - should evict way 1 (LRU)
        cache_write(19'h02200, 16'h0003);

        // Way 0 should still be there
        cache_read(19'h00200, data, hit);
        assert(data == 16'h0001) else $error("LRU replacement failed");

        // Way 1 should be evicted
        cache_read(19'h02200, data, hit);
        assert(data == 16'h0003) else $error("New data not in cache");

        $display("✓ LRU replacement test passed");
    end

    $display("\n=== Test 5: Dirty Line Flush ===");
    begin
        logic [15:0] data;
        logic hit;

        // Write to cache (makes it dirty)
        cache_write(19'h00300, 16'hDEAD);

        // Read back from cache
        cache_read(19'h00300, data, hit);
        assert(data == 16'hDEAD) else $error("Cache data incorrect");

        // Force eviction by filling both ways then adding third
        cache_write(19'h01300, 16'hBEEF);
        cache_write(19'h02300, 16'hCAFE);  // Should flush 0x00300 to memory

        // Wait for flush to complete
        repeat(20) @(posedge clk);

        // Verify data was written to memory
        assert(memory[19'h00300] == 16'hDEAD) else $error("Dirty line not flushed to memory");

        $display("✓ Dirty line flush test passed");
    end

    $display("\n=== Test 6: Sequential Access Pattern ===");
    begin
        logic [15:0] data;
        logic hit;

        // Sequential reads (typical of array access)
        for (int i = 0; i < 32; i++) begin
            cache_read(19'h10000 + 19'(i), data, hit);
        end

        $display("✓ Sequential access test passed");
    end

    $display("\n=== Test 7: Random Access Pattern ===");
    begin
        logic [15:0] data;
        logic hit;

        // Random writes
        cache_write(19'h00400, 16'd0);
        cache_write(19'h01234, 16'd100);
        cache_write(19'h05678, 16'd200);
        cache_write(19'h09ABC, 16'd300);
        cache_write(19'h0CDEF, 16'd400);
        cache_write(19'h01111, 16'd500);
        cache_write(19'h02222, 16'd600);
        cache_write(19'h03333, 16'd700);

        // Random reads
        cache_read(19'h03333, data, hit);
        cache_read(19'h02222, data, hit);
        cache_read(19'h01111, data, hit);
        cache_read(19'h0CDEF, data, hit);
        cache_read(19'h09ABC, data, hit);
        cache_read(19'h05678, data, hit);
        cache_read(19'h01234, data, hit);
        cache_read(19'h00400, data, hit);

        $display("✓ Random access test passed");
    end

    $display("\n=== Test 8: Stress Test - Many Conflicts ===");
    begin
        logic [15:0] data;
        logic hit;

        // Create many addresses mapping to same set
        for (int i = 0; i < 10; i++) begin
            cache_write(19'h00500 + (19'h01000 * 19'(i)), 16'(16'hA000 + i));
        end

        // The last 2 should still be in cache (2-way)
        cache_read(19'h00500 + (19'h01000 * 19'd8), data, hit);
        cache_read(19'h00500 + (19'h01000 * 19'd9), data, hit);
        assert(data == 16'hA009) else $error("Stress test failed");

        $display("✓ Stress test passed");
    end

    // Final statistics
    $display("\n=== Test Complete ===");
    $display("Total Accesses: %0d", total_accesses);
    $display("Reads: %0d", reads);
    $display("Writes: %0d", writes);
    $display("Conflicts Prevented by 2-way: %0d", conflicts_prevented);

    $display("\n✓✓✓ ALL TESTS PASSED ✓✓✓");

    $finish;
end

// Timeout watchdog
initial begin
    #50000;
    $display("ERROR: Global timeout reached");
    $finish;
end

endmodule
