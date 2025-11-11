`timescale 1ns/1ps

module icache2way_test();

logic clk = 0;
logic reset;
logic enabled;
logic [19:1] c_addr;
logic [15:0] c_data_in;
logic c_access;
logic c_ack;
logic [19:1] m_addr;
logic [15:0] m_data_in;
logic m_access;
logic m_ack;

logic [15:0] memory [0:1023];

ICache2Way #(.sets(256)) dut (.*);

always #5 clk = ~clk;

always_ff @(posedge clk) begin
    if (m_access && !m_ack) begin
        m_ack <= 1'b1;
        m_data_in <= memory[m_addr[10:1]];
    end else begin
        m_ack <= 1'b0;
    end
end

initial begin
    for (int i = 0; i < 1024; i++)
        memory[i] = 16'(16'hF000 + i);

    reset = 1; enabled = 1; c_access = 0; c_addr = 19'h0;
    repeat(3) @(posedge clk);
    reset = 0;
    repeat(2) @(posedge clk);

    // Test 1
    $display("Test 1: Fetch 0x100");
    c_addr = 19'h00100; c_access = 1;
    wait(c_ack); @(posedge clk);
    if (c_data_in == 16'hF100) $display("✓ PASS"); else $display("✗ FAIL");
    c_access = 0;
    repeat(5) @(posedge clk);

    // Test 2: 2-way test
    $display("Test 2: 2-way associativity");
    c_addr = 19'h00300; c_access = 1;
    wait(c_ack); @(posedge clk); c_access = 0;
    repeat(10) @(posedge clk);

    c_addr = 19'h01300; c_access = 1;
    wait(c_ack); @(posedge clk); c_access = 0;
    repeat(5) @(posedge clk);

    c_addr = 19'h00300; c_access = 1;
    wait(c_ack); @(posedge clk);
    if (c_data_in == 16'hF300) $display("✓ PASS - both in cache"); else $display("✗ FAIL");
    c_access = 0;

    $display("\n=== ICache2Way Tests Complete ===");
    $finish;
end

initial begin #5000; $display("TIMEOUT"); $finish; end

endmodule
