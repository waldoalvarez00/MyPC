// Simplified DCache2Way test for debugging
`timescale 1ns/1ps

module dcache2way_simple_tb();

logic clk = 0;
logic reset;
logic enabled;

// Frontend
logic [19:1] c_addr;
logic [15:0] c_data_in;
logic [15:0] c_data_out;
logic c_access;
logic c_ack;
logic c_wr_en;
logic [1:0] c_bytesel;

// Backend
logic [19:1] m_addr;
logic [15:0] m_data_in;
logic [15:0] m_data_out;
logic m_access;
logic m_ack;
logic m_wr_en;
logic [1:0] m_bytesel;

// Victim writeback interface (tie off unused in simple test)
logic [18:0] vwb_addr;
logic [15:0] vwb_data_out;
logic vwb_access;
logic vwb_ack;
logic vwb_wr_en;
logic [1:0] vwb_bytesel;

// Simple memory model
logic [15:0] memory [0:1023];

// DUT
DCache2Way #(.sets(256)) dut (.*);

// Clock
always #5 clk = ~clk;

// Memory model - simple immediate response
always_ff @(posedge clk) begin
    if (m_access && !m_ack) begin
        m_ack <= 1'b1;
        if (!m_wr_en)
            m_data_in <= memory[m_addr[9:1]];
        else
            memory[m_addr[9:1]] <= m_data_out;
    end else begin
        m_ack <= 1'b0;
    end
end

// Victim writeback memory model - immediate ack
always_ff @(posedge clk) begin
    if (vwb_access && !vwb_ack) begin
        vwb_ack <= 1'b1;
        // Just ack the write, don't need to actually store
    end else begin
        vwb_ack <= 1'b0;
    end
end

// Monitor
always @(posedge clk) begin
    if (c_ack)
        $display("[%0t] CPU ACK: addr=0x%05x data_in=0x%04x wr=%b data_out=0x%04x",
                 $time, c_addr, c_data_in, c_wr_en, c_data_out);
    if (m_ack && !m_wr_en)
        $display("[%0t] MEM READ: addr=0x%05x data=0x%04x", $time, m_addr, m_data_in);
    if (m_ack && m_wr_en)
        $display("[%0t] MEM WRITE: addr=0x%05x data=0x%04x", $time, m_addr, m_data_out);

    // Debug cache state
    if (dut.hit_way0)
        $display("[%0t]   HIT WAY0", $time);
    if (dut.hit_way1)
        $display("[%0t]   HIT WAY1", $time);
end

// Test
initial begin
    $display("=== Simple DCache2Way Test ===");

    // Init memory
    for (int i = 0; i < 1024; i++)
        memory[i] = 16'(i);

    // Reset
    reset = 1;
    enabled = 1;
    c_access = 0;
    c_wr_en = 0;
    c_addr = 19'h0;
    c_data_out = 16'h0;
    c_bytesel = 2'b11;

    repeat(3) @(posedge clk);
    reset = 0;
    repeat(2) @(posedge clk);

    // Test 1: Simple read
    $display("\n--- Test 1: Read addr 0x10 ---");
    c_addr = 19'h00010;
    c_access = 1;

    wait(c_ack);
    @(posedge clk);
    $display("Result: data=0x%04x (expected 0x0010)", c_data_in);
    if (c_data_in != 16'h0010)
        $display("ERROR: Data mismatch!");
    c_access = 0;

    repeat(5) @(posedge clk);

    // Test 2: Read same address (should hit)
    $display("\n--- Test 2: Read addr 0x10 again (hit) ---");
    c_addr = 19'h00010;
    c_access = 1;

    wait(c_ack);
    @(posedge clk);
    $display("Result: data=0x%04x (expected 0x0010)", c_data_in);
    if (c_data_in != 16'h0010)
        $display("ERROR: Data mismatch!");
    c_access = 0;

    repeat(5) @(posedge clk);

    // Test 3: Write
    $display("\n--- Test 3: Write 0xABCD to addr 0x20 ---");
    c_addr = 19'h00020;
    c_data_out = 16'hABCD;
    c_access = 1;
    c_wr_en = 1;

    wait(c_ack);
    $display("Got ack for write");
    @(posedge clk);
    @(posedge clk);  // Hold signals for extra cycle
    $display("Write complete");
    c_access = 0;
    c_wr_en = 0;

    repeat(5) @(posedge clk);

    // Test 4: Read back write
    $display("\n--- Test 4: Read back addr 0x20 ---");
    c_addr = 19'h00020;
    c_access = 1;

    wait(c_ack);
    @(posedge clk);
    $display("Result: data=0x%04x (expected 0xABCD)", c_data_in);
    if (c_data_in != 16'hABCD)
        $display("ERROR: Write-read mismatch!");
    c_access = 0;

    repeat(10) @(posedge clk);
    $display("\n=== Test Complete ===");
    $finish;
end

// Timeout
initial begin
    #10000;
    $display("TIMEOUT");
    $finish;
end

endmodule
