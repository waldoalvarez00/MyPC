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
    integer read_count = 0;
    always @(posedge clka) begin
        if (wren_a) begin
            mem[address_a] = data_a;  // Blocking assign for simulation
        end
        if (read_count < 30) begin
            $display("[%0d] dpram Port A: clk edge, addr_a=0x%03x, writing=%d",
                     read_count, address_a, wren_a);
            read_count = read_count + 1;
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
        `ifdef VERILATOR
        $display("dpram_dif INIT: addr_width_a=%0d, data_width_a=%0d, addr_width_b=%0d, data_width_b=%0d, mem_size=%0d",
                 addr_width_a, data_width_a, addr_width_b, data_width_b, mem_size);
        `endif
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
    integer porta_clk_count = 0;
    reg [11:0] last_addr_a = 0;
    always @(posedge clka) begin
        // Log address changes in boot ROM range (only for boot ROM instance with mem_size=4096)
        if (mem_size == 4096 && address_a >= 12'h900 && address_a <= 12'h910 && address_a != last_addr_a && porta_clk_count >= 500) begin
            $display("[BOOTROM PortA @%0d] addr_a: 0x%03x → 0x%03x, mem[0x%03x]=0x%02x",
                     porta_clk_count, last_addr_a, address_a, address_a, mem[address_a]);
        end
        last_addr_a <= address_a;
        porta_clk_count = porta_clk_count + 1;

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
            // verilator lint_off WIDTH
            if (mem_size == 4096 && address_b >= 11'h480 && address_b <= 11'h4FF) begin
                `ifdef VERILATOR
                $display("[BOOTROM PortB] write: addr_b=0x%03x → mem[0x%03x]=0x%02x, mem[0x%03x]=0x%02x",
                         address_b, {address_b, 1'b0}, data_b[7:0], {address_b, 1'b1}, data_b[15:8]);
                `endif
            end
            // verilator lint_on WIDTH
        end
    end

    // Combinational read for zero-latency access
    assign q_b = {mem[{address_b, 1'b1}], mem[{address_b, 1'b0}]};

endmodule
