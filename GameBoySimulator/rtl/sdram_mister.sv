// SDRAM Model for MiSTer/MyPC2 Verilator Simulation
// This wrapper matches the exact interface used by SDRAMController.sv
//
// Differences from standard SDRAM:
// - s_bytesel is active-low (inverted from standard DQM)
// - s_wr_en replaces we_n

`timescale 1ns / 1ps

module sdram_mister #(
    parameter SIZE_MB = 64,              // Memory size in MB (64 or 128)
    parameter CLK_FREQ_MHZ = 50,         // Clock frequency in MHz
    parameter CAS_LATENCY = 2,           // CAS latency (2 or 3)
    parameter DEBUG = 0                  // Enable debug output
)(
    // Clock
    input  wire        clk,

    // SDRAM interface (matches SDRAMController.sv)
    input  wire        s_clken,          // Clock enable
    input  wire        s_cs_n,           // Chip select (active low)
    input  wire        s_ras_n,          // Row address strobe (active low)
    input  wire        s_cas_n,          // Column address strobe (active low)
    input  wire        s_wr_en,          // Write enable (active low, inverted from we_n)
    input  wire [1:0]  s_bytesel,        // Byte select (active low - inverted from DQM)
    input  wire [12:0] s_addr,           // Address (row/column multiplexed)
    input  wire [1:0]  s_banksel,        // Bank select
    inout  wire [15:0] s_data            // Data bus (bidirectional)
);

    // Convert interface signals to standard SDRAM
    wire we_n = s_wr_en;                 // Active low
    wire [1:0] dqm = ~s_bytesel;         // Convert active-low to active-high

    // Instantiate standard SDRAM model
    sdram_model #(
        .SIZE_MB(SIZE_MB),
        .CLK_FREQ_MHZ(CLK_FREQ_MHZ),
        .CAS_LATENCY(CAS_LATENCY),
        .BURST_LENGTH(1),
        .DEBUG(DEBUG)
    ) sdram (
        .clk(clk),
        .cke(s_clken),
        .cs_n(s_cs_n),
        .ras_n(s_ras_n),
        .cas_n(s_cas_n),
        .we_n(we_n),
        .ba(s_banksel),
        .addr(s_addr),
        .dqm(dqm),
        .dq(s_data)
    );

    // Expose internal memory for C++ access
    // These functions allow direct memory manipulation from Verilator C++

    // DPI-C functions for memory access from C++
    /* verilator public_flat_rw @(posedge clk) */

    export "DPI-C" function sdram_peek;
    export "DPI-C" function sdram_poke;
    export "DPI-C" function sdram_load_bin;

    function automatic int sdram_peek(input int address);
        if (address < SIZE_MB * 1024 * 512) begin
            sdram_peek = sdram.mem[address];
        end else begin
            sdram_peek = 0;
        end
    endfunction

    function automatic void sdram_poke(input int address, input int data);
        if (address < SIZE_MB * 1024 * 512) begin
            sdram.mem[address] = data[15:0];
        end
    endfunction

    // Load binary file into SDRAM
    function automatic int sdram_load_bin(input string filename, input int start_addr);
        integer fd, count, data, addr;
        begin
            fd = $fopen(filename, "rb");
            if (fd == 0) begin
                if (DEBUG) $display("SDRAM: ERROR - Cannot open file %s", filename);
                sdram_load_bin = -1;
                return;
            end

            addr = start_addr;
            count = 0;
            while (!$feof(fd) && addr < SIZE_MB * 1024 * 512) begin
                data = $fgetc(fd);
                if (data != -1) begin
                    // Load byte by byte, combining into 16-bit words (little endian)
                    if (count & 1) begin
                        sdram.mem[addr] = (sdram.mem[addr] & 16'h00FF) | (data << 8);
                        addr = addr + 1;
                    end else begin
                        sdram.mem[addr] = data & 16'h00FF;
                    end
                    count = count + 1;
                end
            end

            $fclose(fd);
            if (DEBUG) $display("SDRAM: Loaded %0d bytes from %s starting at 0x%h", count, filename, start_addr);
            sdram_load_bin = count;
        end
    endfunction

endmodule

// Top-level test wrapper for standalone SDRAM testing
module sdram_test_top #(
    parameter SIZE_MB = 64,
    parameter DEBUG = 1
)(
    input  wire        clk,
    input  wire        reset,

    // Host interface (mimics SDRAMController host side)
    input  wire        h_access,
    input  wire [25:1] h_addr,
    input  wire [15:0] h_wdata,
    output wire [15:0] h_rdata,
    input  wire        h_wr_en,
    input  wire [1:0]  h_bytesel,
    output wire        h_compl,
    output wire        h_config_done
);

    // Internal signals
    wire s_ras_n, s_cas_n, s_wr_en;
    wire [1:0] s_bytesel;
    wire [12:0] s_addr;
    wire s_cs_n, s_clken;
    wire [15:0] s_data;
    wire [1:0] s_banksel;

    // Instantiate SDRAM Controller
    SDRAMController #(
        .size(SIZE_MB * 1024 * 1024),
        .clkf(50000000)
    ) controller (
        .clk(clk),
        .reset(reset),
        .data_m_access(h_access),
        .cs(1'b1),
        .h_addr(h_addr),
        .h_wdata(h_wdata),
        .h_rdata(h_rdata),
        .h_wr_en(h_wr_en),
        .h_bytesel(h_bytesel),
        .h_compl(h_compl),
        .h_config_done(h_config_done),
        .s_ras_n(s_ras_n),
        .s_cas_n(s_cas_n),
        .s_wr_en(s_wr_en),
        .s_bytesel(s_bytesel),
        .s_addr(s_addr),
        .s_cs_n(s_cs_n),
        .s_clken(s_clken),
        .s_data(s_data),
        .s_banksel(s_banksel)
    );

    // Instantiate SDRAM Model
    sdram_mister #(
        .SIZE_MB(SIZE_MB),
        .CLK_FREQ_MHZ(50),
        .CAS_LATENCY(2),
        .DEBUG(DEBUG)
    ) sdram (
        .clk(clk),
        .s_clken(s_clken),
        .s_cs_n(s_cs_n),
        .s_ras_n(s_ras_n),
        .s_cas_n(s_cas_n),
        .s_wr_en(s_wr_en),
        .s_bytesel(s_bytesel),
        .s_addr(s_addr),
        .s_banksel(s_banksel),
        .s_data(s_data)
    );

endmodule
