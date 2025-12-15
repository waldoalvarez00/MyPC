`timescale 1ns/1ps

module harvard_debug;

reg clk, reset;
reg [19:1] c_addr;
wire [15:0] c_data_in;
reg c_access;
wire c_ack;

wire [19:1] m_addr;
reg [15:0] m_data_in;
wire m_access;
reg m_ack;

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

// Memory model with 2-cycle latency
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
            $display("  [MEM] ACK: addr=0x%05h, data=0x%04h", m_addr, memory[m_addr]);
        end
    end else begin
        m_ack <= 0;
        mem_delay <= 0;
    end
end

// Monitor internal state
always @(posedge clk) begin
    if (c_access || c_ack || m_access) begin
        $display("[%0t] c_addr=0x%05h c_access=%b c_ack=%b c_data=0x%04h | m_addr=0x%05h m_access=%b m_ack=%b | busy=%b updating=%b",
                 $time, c_addr, c_access, c_ack, c_data_in, m_addr, m_access, m_ack,
                 dut.busy, dut.updating);
    end
end

initial begin
    $display("Harvard Cache Debug Test - Immediate Second Fetch");
    reset = 1;
    c_access = 0;
    c_addr = 0;

    repeat(5) @(posedge clk);
    reset = 0;
    repeat(2) @(posedge clk);

    // First fetch
    $display("\n=== FIRST FETCH: 0x100 ===");
    c_addr = 19'h100;
    c_access = 1;
    @(posedge clk);

    while (!c_ack) @(posedge clk);
    $display("✓ First fetch ACK received");

    // Immediately start second fetch (like the testbench does)
    c_access = 0;
    @(posedge clk);

    $display("\n=== SECOND FETCH: 0x101 (immediate) ===");
    c_addr = 19'h101;
    c_access = 1;
    @(posedge clk);

    // Wait with timeout
    begin
        integer timeout;
        timeout = 0;
        while (!c_ack && timeout < 50) begin
            @(posedge clk);
            timeout = timeout + 1;
        end

        if (c_ack) begin
            $display("✓ Second fetch ACK received at cycle %0d", timeout);
            if (c_data_in == (16'h101 ^ 16'hA5A5))
                $display("✓ Data correct: 0x%04h", c_data_in);
            else
                $display("✗ Data wrong: 0x%04h (expected 0x%04h)", c_data_in, 16'h101 ^ 16'hA5A5);
        end else begin
            $display("✗ TIMEOUT on second fetch after %0d cycles", timeout);
        end
    end

    c_access = 0;
    repeat(5) @(posedge clk);

    $display("\nTest complete");
    $finish;
end

endmodule
