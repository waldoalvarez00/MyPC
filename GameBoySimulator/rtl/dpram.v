//
// Dual-Port RAM Module (Verilog replacement for dpram.vhd)
//
// True dual-port RAM with independent or shared clocks
//
// Copyright (c) 2024 - MIT License
//

module dpram #(
    parameter addr_width = 8,
    parameter data_width = 8
) (
    // Single clock (always use this for simulation - dual clocks not supported)
    input                       clock,
    // Dual clocks (unused in this simulation stub - clock is always used)
    input                       clock_a,
    input                       clock_b,

    // Port A
    input  [addr_width-1:0]     address_a,
    input  [data_width-1:0]     data_a,
    input                       wren_a,
    output [data_width-1:0]     q_a,

    // Port B
    input  [addr_width-1:0]     address_b,
    input  [data_width-1:0]     data_b,
    input                       wren_b,
    output [data_width-1:0]     q_b
);

    // For simulation, always use the single 'clock' input
    // The clock_a/clock_b inputs are ignored (they're just compatibility ports)
    wire clka = clock;
    wire clkb = clock;

    // Memory array - initialize to zeros (not random X values)
    // verilator lint_off UNUSEDSIGNAL
    (* ram_init_file = "UNUSED" *)  // Prevent Verilator from randomizing
    reg [data_width-1:0] mem [0:(2**addr_width)-1] /* verilator public */;
    // verilator lint_on UNUSEDSIGNAL

    // Initialize memory to zeros for simulation
    // verilator lint_off BLKSEQ
    integer i;
    initial begin
        for (i = 0; i < (2**addr_width); i = i + 1) begin
            mem[i] = {data_width{1'b0}};
        end
    end
    // verilator lint_on BLKSEQ

    // Port A - Combinational reads for zero-latency access
    // Use BLOCKING assigns (=) for writes to allow combinational reads in same cycle
    always @(posedge clka) begin
        if (wren_a) begin
            mem[address_a] = data_a;  // Blocking assign for simulation
            // Debug: Print writes to HRAM region ($FF80-$FFFE)
            if (addr_width == 7 && $time > 100000) begin  // Only for zpram (7-bit address)
                $display("[DPRAM] @%0t Write to HRAM[$%02X] = $%02X", $time, address_a | 16'hFF80, data_a);
            end
        end
    end

    // Combinational read
    assign q_a = mem[address_a];

    // Port B - Use BLOCKING assigns for writes
    always @(posedge clkb) begin
        if (wren_b) begin
            mem[address_b] = data_b;  // Blocking assign for simulation
        end
    end

    // Combinational read
    assign q_b = mem[address_b];

endmodule

//
// Dual-Port RAM with different widths (dpram_dif)
// Supports both single-clock and dual-clock interfaces
//
module dpram_dif #(
    parameter addr_width_a = 12,
    parameter data_width_a = 8,
    parameter addr_width_b = 11,
    parameter data_width_b = 16,
    parameter init_file = "",
    parameter instance_name = "dpram"
) (
    // Single clock (always use this for simulation - dual clocks not supported)
    input                         clock,
    // Dual clocks (unused in this simulation stub - clock is always used)
    input                         clock_a,
    input                         clock_b,

    // Port A
    input  [addr_width_a-1:0]     address_a,
    input  [data_width_a-1:0]     data_a,
    input                         wren_a,
    output [data_width_a-1:0]     q_a,

    // Port B
    input  [addr_width_b-1:0]     address_b,
    input  [data_width_b-1:0]     data_b,
    input                         wren_b,
    output [data_width_b-1:0]     q_b
);

    // For simulation, always use the single 'clock' input
    // The clock_a/clock_b inputs are ignored (they're just compatibility ports)
    wire clka = clock;
    wire clkb = clock;

    // Use the larger address width for memory
    localparam mem_size = (2**addr_width_a > 2**addr_width_b) ? 2**addr_width_a : 2**addr_width_b;

    // Memory array (using 8-bit granularity)
    (* ram_style = "block" *) reg [7:0] mem [0:mem_size-1] /* verilator public */;

    // Initialize memory from file if specified, otherwise clear to zeros
    integer j;
    initial begin
        if (init_file != "") begin
            $readmemh(init_file, mem);
        end else begin
            // Initialize to zeros for simulation (prevent X propagation)
            for (j = 0; j < mem_size; j = j + 1) begin
                mem[j] = 8'h00;
            end
        end
    end

    // Port A (8-bit access) - Combinational reads for zero-latency access
    // Use BLOCKING assigns (=) for writes to allow combinational reads in same cycle
    always @(posedge clka) begin
        if (wren_a) begin
            mem[address_a] = data_a;  // Blocking assign for simulation
        end
    end

    // Combinational read for zero-latency access
    assign q_a = mem[address_a];

    // Port B (16-bit access, assumes little-endian)
    // Use BLOCKING assigns for writes to allow combinational reads in same cycle
    always @(posedge clkb) begin
        if (wren_b) begin
            mem[{address_b, 1'b0}]     = data_b[7:0];   // Blocking assign
            mem[{address_b, 1'b1}]     = data_b[15:8];  // Blocking assign
        end
    end

    // Combinational read for zero-latency access
    assign q_b = {mem[{address_b, 1'b1}], mem[{address_b, 1'b0}]};

endmodule
