// Copyright 2025, Waldo Alvarez, https://pipflow.com
// Simulation-compatible dual-port RAM for VGA Prefetch
// This module provides a behavioral implementation compatible with Icarus Verilog
// For synthesis, use VGAPrefetchRAM.sv with Altera IP

`timescale 1ns/1ps
`default_nettype none

module VGAPrefetchRAM_sim (
    input wire [8:0]  address_a,
    input wire [8:0]  address_b,
    input wire        clock_a,
    input wire        clock_b,
    input wire [15:0] data_a,
    input wire [15:0] data_b,
    input wire        wren_a,
    input wire        wren_b,
    output reg [15:0] q_a,
    output reg [15:0] q_b
);

    // Dual-port RAM storage: 512 words x 16 bits
    reg [15:0] mem [0:511];

    // Initialize memory to zero for simulation
    integer i;
    initial begin
        for (i = 0; i < 512; i = i + 1) begin
            mem[i] = 16'h0000;
        end
        q_a = 16'h0000;
        q_b = 16'h0000;
    end

    // Port A: sys_clk domain
    always @(posedge clock_a) begin
        if (wren_a) begin
            mem[address_a] <= data_a;
            q_a <= data_a;  // Write-through behavior
        end else begin
            q_a <= mem[address_a];
        end
    end

    // Port B: vga_clk domain
    always @(posedge clock_b) begin
        if (wren_b) begin
            mem[address_b] <= data_b;
            q_b <= data_b;  // Write-through behavior
        end else begin
            q_b <= mem[address_b];
        end
    end

endmodule

`default_nettype wire
