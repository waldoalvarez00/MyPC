`timescale 1ns/1ps
`default_nettype none

// Simplified test focusing ONLY on Test 1 with debug output
module test_icache_second;

reg clk, reset, cache_enabled;

// Instruction bus
reg  [19:1] instr_m_addr;
wire [15:0] instr_m_data_in;
reg         instr_m_access;
wire        instr_m_ack;

// Memory bus
wire [19:1] mem_m_addr;
reg  [15:0] mem_m_data_in;
wire        mem_m_access;
reg         mem_m_ack;

// Memory model
reg [15:0] memory [0:524287];
integer mem_latency, mem_delay_counter;

initial begin
    for (int i = 0; i < 524288; i++)
        memory[i] = i ^ 16'hA5A5;
end

// DUT
HarvardCacheSystem #(
    .ICACHE_LINES(512),
    .DCACHE_LINES(512)
) dut (
    .clk(clk),
    .reset(reset),
    .cache_enabled(cache_enabled),
    .instr_m_addr(instr_m_addr),
    .instr_m_data_in(instr_m_data_in),
    .instr_m_access(instr_m_access),
    .instr_m_ack(instr_m_ack),
    .data_m_addr(19'h0),
    .data_m_data_in(),
    .data_m_data_out(16'h0),
    .data_m_access(1'b0),
    .data_m_ack(),
    .data_m_wr_en(1'b0),
    .data_m_bytesel(2'b11),
    .mem_m_addr(mem_m_addr),
    .mem_m_data_in(mem_m_data_in),
    .mem_m_data_out(),
    .mem_m_access(mem_m_access),
    .mem_m_ack(mem_m_ack),
    .mem_m_wr_en(),
    .mem_m_bytesel()
);

initial begin
    clk = 0;
    forever #10 clk = ~clk;
end

// Memory model
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
            mem_m_data_in <= memory[mem_m_addr];
        end
    end else begin
        mem_m_ack <= 1'b0;
        mem_delay_counter <= 0;
    end
end

// Instruction fetch task (same as testbench)
task instr_fetch(input [19:1] addr, output [15:0] data, output success);
    integer timeout;
begin
    timeout = 0;
    instr_m_addr = addr;
    instr_m_access = 1'b1;
    $display("[DEBUG] instr_fetch: Setting addr=0x%05h, access=1", addr);
    $display("[DEBUG]   Before clk: ack=%b, data=0x%04h", instr_m_ack, instr_m_data_in);
    @(posedge clk);
    $display("[DEBUG]   After 1st clk: ack=%b, data=0x%04h", instr_m_ack, instr_m_data_in);

    while (!instr_m_ack && timeout < 200) begin
        @(posedge clk);
        timeout = timeout + 1;
        $display("[DEBUG]   After clk %0d: ack=%b, data=0x%04h", timeout+1, instr_m_ack, instr_m_data_in);
    end

    if (instr_m_ack) begin
        data = instr_m_data_in;
        success = 1'b1;
        $display("[DEBUG] instr_fetch: GOT ACK after %0d cycles, data=0x%04h", timeout, data);
    end else begin
        data = 16'hXXXX;
        success = 1'b0;
        $display("[DEBUG] instr_fetch: TIMEOUT after %0d cycles", timeout);
    end

    instr_m_access = 1'b0;
    @(posedge clk);
end
endtask

initial begin
    $display("Test I-cache Second Fetch");

    reset = 1;
    cache_enabled = 1;
    instr_m_access = 0;
    mem_latency = 2;

    #100;
    reset = 0;
    #40;

    $display("\n=== Test 1: Basic I-cache Operation ===");
    begin
        reg [15:0] data;
        reg success;

        $display("First fetch: 0x100");
        instr_fetch(19'h00100, data, success);
        if (success && data == (16'h0100 ^ 16'hA5A5))
            $display("✓ First fetch PASS: success=%b, data=0x%04h", success, data);
        else
            $display("✗ First fetch FAIL: success=%b, data=0x%04h (expected 0x%04h)",
                     success, data, 16'h0100 ^ 16'hA5A5);

        // Second fetch from same cache line
        $display("\nSecond fetch: 0x101");
        instr_fetch(19'h00101, data, success);
        if (success && data == (16'h0101 ^ 16'hA5A5))
            $display("✓ Second fetch PASS: success=%b, data=0x%04h", success, data);
        else
            $display("✗ Second fetch FAIL: success=%b, data=0x%04h (expected 0x%04h)",
                     success, data, 16'h0101 ^ 16'hA5A5);
    end

    #100;
    $finish;
end

endmodule
