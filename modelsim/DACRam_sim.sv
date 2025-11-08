// Generic DACRam implementation for simulation
// Replaces Altera altsyncram primitive for Icarus Verilog testing
//
// This is a true dual-port RAM with 256 entries of 18 bits each
// Used for VGA DAC palette storage

`default_nettype none
module DACRam (
    input wire [7:0]  address_a,
    input wire [7:0]  address_b,
    input wire        clock_a,
    input wire        clock_b,
    input wire [17:0] data_a,
    input wire [17:0] data_b,
    input wire        wren_a,
    input wire        wren_b,
    output reg [17:0] q_a,
    output reg [17:0] q_b
);

// Dual-port RAM storage: 256 x 18 bits
reg [17:0] ram [0:255];

// Initialize RAM to zeros
integer i;
initial begin
    for (i = 0; i < 256; i = i + 1) begin
        ram[i] = 18'h00000;
    end
end

// Port A: Read/Write
always_ff @(posedge clock_a) begin
    if (wren_a) begin
        ram[address_a] <= data_a;
    end
    q_a <= ram[address_a];
end

// Port B: Read/Write
always_ff @(posedge clock_b) begin
    if (wren_b) begin
        ram[address_b] <= data_b;
    end
    q_b <= ram[address_b];
end

endmodule
`default_nettype wire
