// SDRAM Model for Verilator Simulation
// Models ISSI IS42S16320B/F - 512Mbit (64MB) SDRAM in 32Mx16 configuration
// Used in MiSTer FPGA SDRAM modules
//
// This model provides cycle-accurate simulation of SDRAM behavior including:
// - All standard SDRAM commands (NOP, ACTIVATE, READ, WRITE, PRECHARGE, REFRESH, MRS)
// - CAS latency pipeline (2 or 3 cycles)
// - Bank/row management with 4 banks
// - Auto-precharge support
// - Byte write masking
// - Configurable timing parameters based on speed grade
//
// Timing specifications based on IS42S16320B datasheet:
// -6 grade: 166MHz, CL2/3, tRCD=18ns, tRP=18ns, tRC=60ns
// -7 grade: 143MHz, CL2/3, tRCD=21ns, tRP=21ns, tRC=66ns
//
// Memory organization:
// - 4 banks x 8192 rows x 1024 columns x 16 bits = 512Mbit = 64MB
// - Address: 13-bit row, 10-bit column, 2-bit bank

`timescale 1ns / 1ps

module sdram_model #(
    parameter SIZE_MB = 64,              // Memory size in MB (64 or 128)
    parameter CLK_FREQ_MHZ = 50,         // Clock frequency in MHz
    parameter CAS_LATENCY = 2,           // CAS latency (2 or 3)
    parameter BURST_LENGTH = 1,          // Burst length (1, 2, 4, 8)
    parameter DEBUG = 0                  // Enable debug output
)(
    input  wire        clk,
    input  wire        cke,              // Clock enable
    input  wire        cs_n,             // Chip select (active low)
    input  wire        ras_n,            // Row address strobe (active low)
    input  wire        cas_n,            // Column address strobe (active low)
    input  wire        we_n,             // Write enable (active low)
    input  wire [1:0]  ba,               // Bank address
    input  wire [12:0] addr,             // Address (row/column multiplexed)
    input  wire [1:0]  dqm,              // Data mask (active high = mask)
    inout  wire [15:0] dq                // Data bus (bidirectional)
);

    // Command decode (active when cs_n = 0)
    localparam CMD_NOP       = 3'b111;   // No operation
    localparam CMD_BST       = 3'b110;   // Burst stop
    localparam CMD_READ      = 3'b101;   // Read
    localparam CMD_WRITE     = 3'b100;   // Write
    localparam CMD_ACTIVATE  = 3'b011;   // Activate row
    localparam CMD_PRECHARGE = 3'b010;   // Precharge
    localparam CMD_REFRESH   = 3'b001;   // Auto refresh
    localparam CMD_MRS       = 3'b000;   // Mode register set

    // Memory array - organized by bank
    // For 64MB: 4 banks x 8192 rows x 1024 columns
    // Using flat array with calculated addresses for Verilator efficiency
    localparam MEM_SIZE = SIZE_MB * 1024 * 1024 / 2;  // Size in 16-bit words
    reg [15:0] mem [0:MEM_SIZE-1];

    // Bank state tracking
    reg [12:0] active_row [0:3];         // Currently active row per bank
    reg [3:0]  row_active;               // Row active flag per bank

    // Mode register
    reg [2:0] mode_cas_latency;
    reg [2:0] mode_burst_length;
    reg       mode_burst_type;           // 0=sequential, 1=interleaved
    reg       mode_write_burst;          // Write burst mode

    // CAS latency read pipeline
    reg [15:0] read_data_pipe [0:3];     // Data pipeline for CAS latency
    reg        read_valid_pipe [0:3];    // Valid flags for pipeline
    reg [1:0]  read_dqm_pipe [0:3];      // DQM pipeline

    // Output enable control
    reg output_enable;
    reg [15:0] dq_out;

    // Internal address calculation
    wire [2:0] cmd = {ras_n, cas_n, we_n};
    wire cmd_valid = ~cs_n && cke;

    // Address decoding for 64MB configuration
    // Bank[1:0] + Row[12:0] + Column[9:0] = 25 bits = 32M addresses x 16 bits = 64MB
    function automatic [24:0] calc_addr;
        input [1:0]  bank;
        input [12:0] row;
        input [9:0]  col;
        begin
            if (SIZE_MB == 64)
                calc_addr = {bank, row, col};
            else // 128MB - two chips
                calc_addr = {bank, row, col};
        end
    endfunction

    // Initialize memory and state
    initial begin
        integer i;
        for (i = 0; i < MEM_SIZE; i = i + 1) begin
            mem[i] = 16'h0000;
        end
        for (i = 0; i < 4; i = i + 1) begin
            active_row[i] = 13'b0;
            read_data_pipe[i] = 16'h0000;
            read_valid_pipe[i] = 1'b0;
            read_dqm_pipe[i] = 2'b00;
        end
        row_active = 4'b0;
        mode_cas_latency = CAS_LATENCY;
        mode_burst_length = BURST_LENGTH;
        mode_burst_type = 1'b0;
        mode_write_burst = 1'b0;
        output_enable = 1'b0;
        dq_out = 16'hzzzz;
    end

    // Bidirectional data bus
    assign dq = output_enable ? dq_out : 16'hzzzz;

    // Main SDRAM state machine
    always @(posedge clk) begin
        // Shift read pipeline
        read_data_pipe[3] <= read_data_pipe[2];
        read_data_pipe[2] <= read_data_pipe[1];
        read_data_pipe[1] <= read_data_pipe[0];

        read_valid_pipe[3] <= read_valid_pipe[2];
        read_valid_pipe[2] <= read_valid_pipe[1];
        read_valid_pipe[1] <= read_valid_pipe[0];

        read_dqm_pipe[3] <= read_dqm_pipe[2];
        read_dqm_pipe[2] <= read_dqm_pipe[1];
        read_dqm_pipe[1] <= read_dqm_pipe[0];

        // Clear stage 0 by default
        read_valid_pipe[0] <= 1'b0;
        read_dqm_pipe[0] <= 2'b00;

        // Output data based on CAS latency
        if (mode_cas_latency == 2) begin
            output_enable <= read_valid_pipe[1];
            if (read_valid_pipe[1]) begin
                // Apply DQM masking
                dq_out <= {read_dqm_pipe[1][1] ? 8'hzz : read_data_pipe[1][15:8],
                          read_dqm_pipe[1][0] ? 8'hzz : read_data_pipe[1][7:0]};
            end
        end else begin // CAS latency 3
            output_enable <= read_valid_pipe[2];
            if (read_valid_pipe[2]) begin
                dq_out <= {read_dqm_pipe[2][1] ? 8'hzz : read_data_pipe[2][15:8],
                          read_dqm_pipe[2][0] ? 8'hzz : read_data_pipe[2][7:0]};
            end
        end

        // Process commands
        if (cmd_valid) begin
            case (cmd)
                CMD_ACTIVATE: begin
                    // Activate a row in the specified bank
                    active_row[ba] <= addr;
                    row_active[ba] <= 1'b1;
                    if (DEBUG) begin
                        $display("[%0t] SDRAM: ACTIVATE bank=%0d row=0x%h", $time, ba, addr);
                    end
                end

                CMD_READ: begin
                    // Read from active row
                    if (row_active[ba]) begin
                        reg [24:0] read_addr;
                        reg [15:0] read_data;

                        read_addr = calc_addr(ba, active_row[ba], addr[9:0]);
                        read_data = mem[read_addr];

                        // Insert into pipeline stage 0
                        read_data_pipe[0] <= read_data;
                        read_valid_pipe[0] <= 1'b1;
                        read_dqm_pipe[0] <= dqm;

                        if (DEBUG) begin
                            $display("[%0t] SDRAM: READ bank=%0d col=0x%h addr=0x%h data=0x%h",
                                     $time, ba, addr[9:0], read_addr, read_data);
                        end

                        // Auto-precharge if A10 is set
                        if (addr[10]) begin
                            row_active[ba] <= 1'b0;
                            if (DEBUG) begin
                                $display("[%0t] SDRAM: AUTO-PRECHARGE bank=%0d", $time, ba);
                            end
                        end
                    end else begin
                        if (DEBUG) begin
                            $display("[%0t] SDRAM: ERROR - READ to inactive bank %0d", $time, ba);
                        end
                    end
                end

                CMD_WRITE: begin
                    // Write to active row
                    if (row_active[ba]) begin
                        reg [24:0] write_addr;
                        reg [15:0] write_data;

                        write_addr = calc_addr(ba, active_row[ba], addr[9:0]);
                        write_data = dq;

                        // Apply byte mask (DQM active high = mask write)
                        if (~dqm[0]) mem[write_addr][7:0]  <= write_data[7:0];
                        if (~dqm[1]) mem[write_addr][15:8] <= write_data[15:8];

                        if (DEBUG) begin
                            $display("[%0t] SDRAM: WRITE bank=%0d col=0x%h addr=0x%h data=0x%h dqm=%b",
                                     $time, ba, addr[9:0], write_addr, write_data, dqm);
                        end

                        // Auto-precharge if A10 is set
                        if (addr[10]) begin
                            row_active[ba] <= 1'b0;
                            if (DEBUG) begin
                                $display("[%0t] SDRAM: AUTO-PRECHARGE bank=%0d", $time, ba);
                            end
                        end
                    end else begin
                        if (DEBUG) begin
                            $display("[%0t] SDRAM: ERROR - WRITE to inactive bank %0d", $time, ba);
                        end
                    end
                end

                CMD_PRECHARGE: begin
                    // Precharge bank(s)
                    if (addr[10]) begin
                        // Precharge all banks
                        row_active <= 4'b0;
                        if (DEBUG) begin
                            $display("[%0t] SDRAM: PRECHARGE ALL", $time);
                        end
                    end else begin
                        // Precharge single bank
                        row_active[ba] <= 1'b0;
                        if (DEBUG) begin
                            $display("[%0t] SDRAM: PRECHARGE bank=%0d", $time, ba);
                        end
                    end
                end

                CMD_REFRESH: begin
                    // Auto refresh - all rows must be precharged
                    row_active <= 4'b0;
                    if (DEBUG) begin
                        $display("[%0t] SDRAM: AUTO REFRESH", $time);
                    end
                end

                CMD_MRS: begin
                    // Mode register set
                    mode_burst_length <= addr[2:0];
                    mode_burst_type   <= addr[3];
                    mode_cas_latency  <= addr[6:4];
                    mode_write_burst  <= addr[9];

                    if (DEBUG) begin
                        $display("[%0t] SDRAM: MODE REGISTER SET - BL=%0d, BT=%0d, CL=%0d, WB=%0d",
                                 $time, addr[2:0], addr[3], addr[6:4], addr[9]);
                    end
                end

                CMD_BST: begin
                    // Burst stop
                    output_enable <= 1'b0;
                    read_valid_pipe[0] <= 1'b0;
                    read_valid_pipe[1] <= 1'b0;
                    read_valid_pipe[2] <= 1'b0;
                    if (DEBUG) begin
                        $display("[%0t] SDRAM: BURST STOP", $time);
                    end
                end

                CMD_NOP: begin
                    // No operation - do nothing
                end

                default: begin
                    // Unknown command
                end
            endcase
        end
    end

    // Memory initialization from file (optional)
    // Can be called from testbench or C++ code
    task load_memory;
        input [255:0] filename;
        begin
            $readmemh(filename, mem);
            if (DEBUG) begin
                $display("[%0t] SDRAM: Loaded memory from %s", $time, filename);
            end
        end
    endtask

    // Memory dump for debugging
    task dump_memory;
        input [24:0] start_addr;
        input [24:0] end_addr;
        integer i;
        begin
            $display("SDRAM Memory Dump [0x%h - 0x%h]:", start_addr, end_addr);
            for (i = start_addr; i <= end_addr && i < MEM_SIZE; i = i + 1) begin
                if (mem[i] != 16'h0000) begin
                    $display("  [0x%06h] = 0x%04h", i, mem[i]);
                end
            end
        end
    endtask

    // Direct memory access for verification (bypasses SDRAM protocol)
    function [15:0] peek;
        input [24:0] address;
        begin
            peek = mem[address];
        end
    endfunction

    task poke;
        input [24:0] address;
        input [15:0] data;
        begin
            mem[address] = data;
        end
    endtask

endmodule

// Dual-chip 128MB SDRAM model wrapper (for MiSTer 128MB configurations)
module sdram_model_128mb #(
    parameter CLK_FREQ_MHZ = 50,
    parameter CAS_LATENCY = 2,
    parameter BURST_LENGTH = 1,
    parameter DEBUG = 0
)(
    input  wire        clk,
    input  wire        cke,
    input  wire        cs_n,
    input  wire        ras_n,
    input  wire        cas_n,
    input  wire        we_n,
    input  wire [1:0]  ba,
    input  wire [12:0] addr,
    input  wire [1:0]  dqm,
    inout  wire [15:0] dq,
    input  wire        chip_sel      // Selects between two 64MB chips
);

    wire [15:0] dq_chip0, dq_chip1;
    wire cs_n_chip0 = cs_n | chip_sel;
    wire cs_n_chip1 = cs_n | ~chip_sel;

    // Chip 0 - Lower 64MB
    sdram_model #(
        .SIZE_MB(64),
        .CLK_FREQ_MHZ(CLK_FREQ_MHZ),
        .CAS_LATENCY(CAS_LATENCY),
        .BURST_LENGTH(BURST_LENGTH),
        .DEBUG(DEBUG)
    ) chip0 (
        .clk(clk),
        .cke(cke),
        .cs_n(cs_n_chip0),
        .ras_n(ras_n),
        .cas_n(cas_n),
        .we_n(we_n),
        .ba(ba),
        .addr(addr),
        .dqm(dqm),
        .dq(dq_chip0)
    );

    // Chip 1 - Upper 64MB
    sdram_model #(
        .SIZE_MB(64),
        .CLK_FREQ_MHZ(CLK_FREQ_MHZ),
        .CAS_LATENCY(CAS_LATENCY),
        .BURST_LENGTH(BURST_LENGTH),
        .DEBUG(DEBUG)
    ) chip1 (
        .clk(clk),
        .cke(cke),
        .cs_n(cs_n_chip1),
        .ras_n(ras_n),
        .cas_n(cas_n),
        .we_n(we_n),
        .ba(ba),
        .addr(addr),
        .dqm(dqm),
        .dq(dq_chip1)
    );

    // Mux data bus based on chip select
    assign dq = ~cs_n_chip0 ? dq_chip0 : (~cs_n_chip1 ? dq_chip1 : 16'hzzzz);

endmodule
