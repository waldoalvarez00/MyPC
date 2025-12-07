//
// Dual-Port RAM Module (Verilog replacement for dpram.vhd)
//
// Simple dual-port RAM with independent read/write ports
//
// Copyright (c) 2024 - MIT License
//

module dpram #(
    parameter addr_width = 8,
    parameter data_width = 8
) (
    input                       clock,

    // Port A (primary)
    input  [addr_width-1:0]     address_a,
    input  [data_width-1:0]     data_a,
    input                       wren_a,
    output reg [data_width-1:0] q_a,

    // Port B (secondary)
    input  [addr_width-1:0]     address_b,
    input  [data_width-1:0]     data_b,
    input                       wren_b,
    output reg [data_width-1:0] q_b
);

    // Memory array
    reg [data_width-1:0] mem [0:(2**addr_width)-1];

    // Port A
    always @(posedge clock) begin
        if (wren_a) begin
            mem[address_a] <= data_a;
        end
        q_a <= mem[address_a];
    end

    // Port B
    always @(posedge clock) begin
        if (wren_b) begin
            mem[address_b] <= data_b;
        end
        q_b <= mem[address_b];
    end

endmodule

//
// Dual-Port RAM with different widths (dpram_dif)
//
module dpram_dif #(
    parameter addr_width_a = 12,
    parameter data_width_a = 8,
    parameter addr_width_b = 11,
    parameter data_width_b = 16,
    parameter init_file = ""
) (
    input                         clock,

    // Port A
    input  [addr_width_a-1:0]     address_a,
    input  [data_width_a-1:0]     data_a,
    input                         wren_a,
    output reg [data_width_a-1:0] q_a,

    // Port B
    input  [addr_width_b-1:0]     address_b,
    input  [data_width_b-1:0]     data_b,
    input                         wren_b,
    output reg [data_width_b-1:0] q_b
);

    // Use the larger address width for memory
    localparam mem_size = (2**addr_width_a > 2**addr_width_b) ? 2**addr_width_a : 2**addr_width_b;

    // Memory array (using 8-bit granularity)
    reg [7:0] mem [0:mem_size-1];

    // Initialize memory from file if specified
    initial begin
        if (init_file != "") begin
            $readmemh(init_file, mem);
        end
    end

    // Port A (8-bit access)
    always @(posedge clock) begin
        if (wren_a) begin
            mem[address_a] <= data_a;
        end
        q_a <= mem[address_a];
    end

    // Port B (16-bit access, assumes little-endian)
    always @(posedge clock) begin
        if (wren_b) begin
            mem[{address_b, 1'b0}]     <= data_b[7:0];
            mem[{address_b, 1'b1}]     <= data_b[15:8];
        end
        q_b <= {mem[{address_b, 1'b1}], mem[{address_b, 1'b0}]};
    end

endmodule
