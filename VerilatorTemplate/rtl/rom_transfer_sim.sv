// ROM Transfer Simulation Module
// Simple interface for testing ROM loading to SDRAM
//
// Receives ROM data from testbench and writes to SDRAM

`timescale 1ns / 1ps

module rom_transfer_sim (
    input  wire        clk,
    input  wire        reset,

    // Control interface
    input  wire        start,       // Start transfer
    output reg         busy,        // Transfer in progress
    output reg         ready,       // Ready for next word
    output reg         done,        // Transfer complete

    // Data input from testbench
    input  wire [22:0] addr_in,     // Word address
    input  wire [15:0] data_in,     // Data to write
    input  wire        data_valid,  // Data valid strobe

    // SDRAM interface (directly exposed for C++ model)
    output reg         sd_cs,       // Chip select (directly active)
    output reg         sd_ras,      // RAS
    output reg         sd_cas,      // CAS
    output reg         sd_we,       // WE
    output reg  [1:0]  sd_ba,       // Bank address
    output reg  [12:0] sd_addr,     // Address
    output reg  [1:0]  sd_dqm,      // Data mask
    output reg  [15:0] sd_dq_out,   // Data output
    input  wire [15:0] sd_dq_in,    // Data input

    // Status
    output reg  [31:0] words_written
);

// State machine
localparam STATE_IDLE       = 3'd0;
localparam STATE_INIT       = 3'd1;
localparam STATE_PRECHARGE  = 3'd2;
localparam STATE_MRS        = 3'd3;
localparam STATE_ACTIVATE   = 3'd4;
localparam STATE_WRITE      = 3'd5;
localparam STATE_WAIT       = 3'd6;

reg [2:0] state;
reg [3:0] wait_count;
reg       initialized;

// Address breakdown for SDRAM
// Based on Gameboy controller scheme:
// - Bank: addr[21:20]
// - Row: addr[19:8]
// - Col: {addr[22], addr[7:0]}
wire [1:0]  bank = addr_in[21:20];
wire [12:0] row  = addr_in[19:8];
wire [9:0]  col  = {addr_in[22], addr_in[7:0]};

// Track current active row per bank
reg [12:0] active_row [0:3];
reg [3:0]  row_active;

// Latched data for write
reg [22:0] write_addr;
reg [15:0] write_data;

// Command encoding (directly set output signals)
task cmd_nop;
    begin
        sd_cs  <= 0;
        sd_ras <= 1;
        sd_cas <= 1;
        sd_we  <= 1;
    end
endtask

task cmd_activate(input [1:0] ba, input [12:0] addr);
    begin
        sd_cs   <= 0;
        sd_ras  <= 0;
        sd_cas  <= 1;
        sd_we   <= 1;
        sd_ba   <= ba;
        sd_addr <= addr;
    end
endtask

task cmd_write(input [1:0] ba, input [9:0] col_addr, input [15:0] data);
    begin
        sd_cs     <= 0;
        sd_ras    <= 1;
        sd_cas    <= 0;
        sd_we     <= 0;
        sd_ba     <= ba;
        sd_addr   <= {3'b001, col_addr};  // A10=1 for auto-precharge
        sd_dq_out <= data;
        sd_dqm    <= 2'b00;  // No masking
    end
endtask

task cmd_precharge_all;
    begin
        sd_cs   <= 0;
        sd_ras  <= 0;
        sd_cas  <= 1;
        sd_we   <= 0;
        sd_addr <= 13'b0010000000000;  // A10=1 for all banks
    end
endtask

task cmd_mrs(input [12:0] mode);
    begin
        sd_cs   <= 0;
        sd_ras  <= 0;
        sd_cas  <= 0;
        sd_we   <= 0;
        sd_ba   <= 2'b00;
        sd_addr <= mode;
    end
endtask

// State machine
always @(posedge clk or posedge reset) begin
    if (reset) begin
        state <= STATE_IDLE;
        busy <= 0;
        ready <= 0;
        done <= 0;
        initialized <= 0;
        wait_count <= 0;
        words_written <= 0;
        row_active <= 4'b0000;

        // Default to NOP
        sd_cs <= 0;
        sd_ras <= 1;
        sd_cas <= 1;
        sd_we <= 1;
        sd_ba <= 0;
        sd_addr <= 0;
        sd_dqm <= 2'b11;
        sd_dq_out <= 0;

        for (int i = 0; i < 4; i++) begin
            active_row[i] <= 0;
        end
    end else begin
        case (state)
            STATE_IDLE: begin
                cmd_nop();
                ready <= 1;
                busy <= 0;

                if (start && !initialized) begin
                    // Initialize SDRAM
                    state <= STATE_INIT;
                    ready <= 0;
                    busy <= 1;
                    wait_count <= 10;  // Wait for power-up
                end else if (data_valid) begin
                    // Latch write data
                    write_addr <= addr_in;
                    write_data <= data_in;
                    ready <= 0;
                    busy <= 1;

                    // Check if row is already active
                    if (row_active[bank] && active_row[bank] == row) begin
                        // Row already active, go directly to write
                        state <= STATE_WRITE;
                    end else begin
                        // Need to activate row
                        state <= STATE_ACTIVATE;
                    end
                end
            end

            STATE_INIT: begin
                if (wait_count > 0) begin
                    cmd_nop();
                    wait_count <= wait_count - 1;
                end else begin
                    // Precharge all banks
                    cmd_precharge_all();
                    state <= STATE_PRECHARGE;
                    wait_count <= 2;
                end
            end

            STATE_PRECHARGE: begin
                if (wait_count > 0) begin
                    cmd_nop();
                    wait_count <= wait_count - 1;
                end else begin
                    // Set mode register
                    // CAS latency 2, burst length 1
                    cmd_mrs(13'b0000000100000);
                    state <= STATE_MRS;
                    wait_count <= 2;
                end
            end

            STATE_MRS: begin
                if (wait_count > 0) begin
                    cmd_nop();
                    wait_count <= wait_count - 1;
                end else begin
                    initialized <= 1;
                    state <= STATE_IDLE;
                end
            end

            STATE_ACTIVATE: begin
                // Calculate bank and row from latched address
                cmd_activate(write_addr[21:20], write_addr[19:8]);
                active_row[write_addr[21:20]] <= write_addr[19:8];
                row_active[write_addr[21:20]] <= 1;
                state <= STATE_WAIT;
                wait_count <= 2;  // tRCD
            end

            STATE_WAIT: begin
                if (wait_count > 0) begin
                    cmd_nop();
                    wait_count <= wait_count - 1;
                end else begin
                    state <= STATE_WRITE;
                end
            end

            STATE_WRITE: begin
                // Issue write command with auto-precharge
                cmd_write(
                    write_addr[21:20],
                    {write_addr[22], write_addr[7:0]},
                    write_data
                );
                // Auto-precharge will close the row
                row_active[write_addr[21:20]] <= 0;
                words_written <= words_written + 1;
                state <= STATE_IDLE;
                wait_count <= 0;
            end

            default: begin
                state <= STATE_IDLE;
            end
        endcase
    end
end

endmodule
