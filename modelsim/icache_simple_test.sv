`timescale 1ns/1ps

module icache_simple_test;

reg clk, reset;
reg [19:1] c_addr;
wire [15:0] c_data_in;
reg c_access;
wire c_ack;

wire [19:1] m_addr;
reg [15:0] m_data_in;
wire m_access;
reg m_ack;

// Simple memory model
reg [15:0] memory [0:1023];
integer mem_delay;

initial begin
    for (int i = 0; i < 1024; i++)
        memory[i] = i ^ 16'hA5A5;
end

ICache #(.lines(512)) dut (
    .clk(clk),
    .reset(reset),
    .enabled(1'b1),
    .c_addr(c_addr),
    .c_data_in(c_data_in),
    .c_access(c_access),
    .c_ack(c_ack),
    .m_addr(m_addr),
    .m_data_in(m_data_in),
    .m_access(m_access),
    .m_ack(m_ack)
);

initial begin
    clk = 0;
    forever #10 clk = ~clk;
end

// Memory model
always @(posedge clk) begin
    if (reset) begin
        m_ack <= 0;
        mem_delay <= 0;
    end else if (m_access && !m_ack) begin
        if (mem_delay < 2) begin
            mem_delay <= mem_delay + 1;
            m_ack <= 0;
        end else begin
            m_ack <= 1;
            m_data_in <= memory[m_addr];
        end
    end else begin
        m_ack <= 0;
        mem_delay <= 0;
    end
end

initial begin
    $display("ICache Simple Test");
    reset = 1;
    c_access = 0;
    c_addr = 0;

    repeat(5) @(posedge clk);
    reset = 0;
    repeat(2) @(posedge clk);

    // Test 1: Fetch from 0x100
    $display("\n[Test 1] Fetch from 0x100");
    c_addr = 19'h100;
    c_access = 1;
    @(posedge clk);

    while (!c_ack) begin
        @(posedge clk);
        if (c_ack) begin
            $display("  ✓ Got ack, data=0x%04h", c_data_in);
        end
    end

    if (!c_ack) begin
        $display("  ✗ TIMEOUT waiting for ack");
        $finish;
    end

    c_access = 0;
    @(posedge clk);

    // Wait for fill to potentially complete
    repeat(20) @(posedge clk);

    // Test 2: Fetch from 0x101 (same cache line)
    $display("\n[Test 2] Fetch from 0x101 (same line as 0x100)");
    c_addr = 19'h101;
    c_access = 1;
    @(posedge clk);

    while (!c_ack) begin
        @(posedge clk);
        if (c_ack) begin
            $display("  ✓ Got ack, data=0x%04h", c_data_in);
            if (c_data_in == (16'h101 ^ 16'hA5A5))
                $display("  ✓ Data matches expected value");
            else
                $display("  ✗ Data mismatch! Expected 0x%04h", 16'h101 ^ 16'hA5A5);
        end
    end

    if (!c_ack) begin
        $display("  ✗ TIMEOUT waiting for ack on second fetch");
    end

    c_access = 0;
    @(posedge clk);

    $display("\nTest complete");
    $finish;
end

endmodule
