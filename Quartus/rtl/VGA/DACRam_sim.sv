// Simulation-compatible DAC RAM for VGA 256-color palette
// This module provides a behavioral implementation compatible with Icarus Verilog
// For synthesis, use DACRam.v with Altera IP

`timescale 1ns/1ps

module DACRam_sim (
    input wire [7:0]   address_a,
    input wire [7:0]   address_b,
    input wire         clock_a,
    input wire         clock_b,
    input wire [17:0]  data_a,
    input wire [17:0]  data_b,
    input wire         wren_a,
    input wire         wren_b,
    output reg [17:0]  q_a,
    output reg [17:0]  q_b
);

    // DAC RAM storage: 256 entries x 18 bits (6 bits per RGB channel)
    reg [17:0] mem [0:255];

    // Initialize with default VGA palette
    integer i;
    initial begin
        // Initialize with basic VGA colors
        // Format: {R[17:12], G[11:6], B[5:0]} - 6 bits per channel

        // Standard 16 EGA colors (entries 0-15)
        mem[0]  = 18'h00000;  // Black
        mem[1]  = 18'h0002A;  // Blue
        mem[2]  = 18'h00A00;  // Green
        mem[3]  = 18'h00A2A;  // Cyan
        mem[4]  = 18'h28000;  // Red
        mem[5]  = 18'h2802A;  // Magenta
        mem[6]  = 18'h28A00;  // Brown
        mem[7]  = 18'h2AA2A;  // Light Gray
        mem[8]  = 18'h15555;  // Dark Gray
        mem[9]  = 18'h1557F;  // Light Blue
        mem[10] = 18'h15F55;  // Light Green
        mem[11] = 18'h15F7F;  // Light Cyan
        mem[12] = 18'h3F555;  // Light Red
        mem[13] = 18'h3F57F;  // Light Magenta
        mem[14] = 18'h3FF55;  // Yellow
        mem[15] = 18'h3FF7F;  // White

        // Initialize remaining palette with gradient (entries 16-255)
        for (i = 16; i < 256; i = i + 1) begin
            mem[i] = {6'(i/4), 6'(i/4), 6'(i/4)};  // Grayscale gradient
        end

        // Initialize outputs
        q_a = 18'h00000;
        q_b = 18'h00000;
    end

    // Port A: sys_clk domain (write port for CPU)
    always @(posedge clock_a) begin
        if (wren_a) begin
            mem[address_a] <= data_a;
            q_a <= data_a;  // Write-through
        end else begin
            q_a <= mem[address_a];
        end
    end

    // Port B: vga_clk domain (read port for VGA)
    always @(posedge clock_b) begin
        if (wren_b) begin
            mem[address_b] <= data_b;
            q_b <= data_b;  // Write-through
        end else begin
            q_b <= mem[address_b];
        end
    end

endmodule
