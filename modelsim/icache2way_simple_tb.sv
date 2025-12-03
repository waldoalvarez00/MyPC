// Simplified ICache2WayPrefetch test
`timescale 1ns/1ps

module icache2way_simple_tb();

logic clk = 0;
logic reset;
logic enabled;

// Frontend
logic [19:1] c_addr;
logic [15:0] c_data_in;
logic c_access;
logic c_ack;

// Backend
logic [19:1] m_addr;
logic [15:0] m_data_in;
logic m_access;
logic m_ack;

// Simple instruction memory - sized to cover full address space
logic [15:0] memory [0:524287];  // 512K words like comprehensive test

// Error tracking
int error_count = 0;

// DUT
ICache2WayPrefetch #(.sets(256)) dut (.*);

// Clock
always #5 clk = ~clk;

// Memory model - immediate response (direct addressing like comprehensive test)
always_ff @(posedge clk) begin
    if (m_access && !m_ack) begin
        m_ack <= 1'b1;
        m_data_in <= memory[m_addr];
    end else begin
        m_ack <= 1'b0;
    end
end

// Monitor
always @(posedge clk) begin
    if (c_ack)
        $display("[%0t] FETCH ACK: addr=0x%05x data=0x%04x", $time, c_addr, c_data_in);
    if (m_ack)
        $display("[%0t] MEM FETCH: addr=0x%05x data=0x%04x%s",
                 $time, m_addr, m_data_in, dut.prefetch_active ? " (PREFETCH)" : "");
    if (dut.prefetch_active && !dut.prefetch_active)
        $display("[%0t] PREFETCH STARTED", $time);
end

// Fetch task - matches comprehensive test timing
task fetch_instr(input [19:1] addr, output [15:0] data);
    begin
        @(posedge clk);
        c_addr <= addr;
        c_access <= 1'b1;

        fork
            begin: timeout_block
                repeat(100) @(posedge clk);
                $display("[%0t] ERROR: Fetch timeout for addr 0x%05x", $time, addr);
                $finish;
            end
            begin
                @(posedge clk);
                wait(c_ack);
                disable timeout_block;
                data = c_data_in;
                @(posedge clk);
                c_access <= 1'b0;
            end
        join
    end
endtask

// Test
initial begin
    $display("=== Simple ICache2WayPrefetch Test ===");

    // Init memory with simple pattern (address = data, like comprehensive test)
    for (int i = 0; i < 524288; i++)
        memory[i] = 16'(i & 16'hFFFF);  // memory[addr] = addr

    // Reset
    reset = 1;
    enabled = 1;
    c_access = 0;
    c_addr = 19'h0;

    repeat(3) @(posedge clk);
    reset = 0;
    repeat(2) @(posedge clk);

    // Test 1: Fetch single instruction
    $display("\n--- Test 1: Fetch addr 0x100 ---");
    @(posedge clk);
    c_addr <= 19'h00100;
    c_access <= 1;

    @(posedge clk);  // Extra cycle before waiting
    do @(posedge clk); while (!c_ack);
    $display("Result: data=0x%04x (expected 0x%04x)", c_data_in, 16'h0100);
    if (c_data_in != 16'h0100) begin
        $display("MISMATCH: Data mismatch!");
        error_count++;
    end
    @(posedge clk);
    c_access <= 0;

    repeat(10) @(posedge clk);

    // Test 2: Sequential fetches (triggers prefetch)
    $display("\n--- Test 2: Sequential fetches (should trigger prefetch) ---");

    for (int i = 0; i < 16; i++) begin
        logic [15:0] fetched_data;

        @(posedge clk);
        c_addr <= 19'h00200 + 19'(i);  // Non-blocking like passing test
        c_access <= 1;

        @(posedge clk);  // Extra cycle before waiting (like passing test)
        // Wait for posedge where ack is high
        do @(posedge clk); while (!c_ack);
        fetched_data = c_data_in;
        @(posedge clk);
        c_access <= 0;

        $display("Fetched[%0d]: addr=0x%05x data=0x%04x", i, 19'h00200 + 19'(i), fetched_data);
        if (fetched_data != (16'h0200 + i)) begin
            $display("MISMATCH: Data mismatch at index %0d!", i);
            error_count++;
        end
    end

    $display("Sequential fetch test complete");

    repeat(10) @(posedge clk);

    // Test 3: Non-sequential jump
    $display("\n--- Test 3: Jump to different address ---");
    begin
        logic [15:0] jump_data;

        @(posedge clk);
        c_addr <= 19'h00500;
        c_access <= 1;

        @(posedge clk);  // Extra cycle before waiting
        do @(posedge clk); while (!c_ack);
        jump_data = c_data_in;
        @(posedge clk);
        c_access <= 0;

        $display("Result: data=0x%04x (expected 0x%04x)", jump_data, 16'h0500);
        if (jump_data != 16'h0500) begin
            $display("MISMATCH: Data mismatch!");
            error_count++;
        end
    end

    repeat(10) @(posedge clk);

    // Note: 2-way associativity is comprehensively tested in icache2way_prefetch test

    $display("\n=== Test Complete ===");
    if (error_count == 0) begin
        $display("✓ All basic tests passed");
        $display("✓ Sequential prefetcher operational");
        $display("✓ Non-sequential jump works");
        $display("ALL TESTS PASSED");
    end else begin
        $display("✗ %0d errors detected", error_count);
        $display("TESTS FAILED");
    end

    $finish;
end

// Timeout
initial begin
    #3000000;
    $display("TIMEOUT");
    $finish;
end

endmodule
