// Simulation-friendly SDRAM Controller
// Based on MiSTer Gameboy SDRAM controller by Till Harbaum & Sorgelig
// Modified for Verilator simulation (removed Altera-specific primitives)
//
// This controller provides 8-cycle access at 64MHz (emulates 8MHz async DRAM)

`timescale 1ns / 1ps

module sdram_ctrl_sim
(
    // Interface to SDRAM chip (directly connects to C++ model)
    output reg [15:0] sd_data_out,  // Data output to SDRAM
    input      [15:0] sd_data_in,   // Data input from SDRAM
    output reg        sd_data_oe,   // Output enable for data bus
    output reg [12:0] sd_addr,      // 13 bit multiplexed address bus
    output     [1:0]  sd_dqm,       // Two byte masks
    output reg [1:0]  sd_ba,        // Two banks
    output            sd_cs,        // Chip select
    output            sd_we,        // Write enable
    output            sd_ras,       // Row address select
    output            sd_cas,       // Column address select

    // CPU/chipset interface
    input             init,         // Init signal to initialize RAM
    input             clk,          // SDRAM clock (64MHz)
    input             sync,         // Sync pulse

    input      [15:0] din,          // Data input from CPU
    output reg [15:0] dout,         // Data output to CPU
    input      [23:0] addr,         // 24 bit word address
    input      [1:0]  ds,           // Upper/lower data strobe
    input             oe,           // CPU requests read
    input             we,           // CPU requests write
    input             autorefresh,  // Autorefresh when idle
    input             refresh       // Force refresh
);

localparam RASCAS_DELAY   = 3'd2;   // tRCD cycles
localparam BURST_LENGTH   = 3'b000; // 1
localparam ACCESS_TYPE    = 1'b0;   // Sequential
localparam CAS_LATENCY    = 3'd2;   // 2 cycles
localparam OP_MODE        = 2'b00;  // Standard
localparam NO_WRITE_BURST = 1'b1;   // Single access write

localparam MODE = { 3'b000, NO_WRITE_BURST, OP_MODE, CAS_LATENCY, ACCESS_TYPE, BURST_LENGTH};

// State machine states
localparam STATE_FIRST     = 3'd0;
localparam STATE_CMD_START = 3'd1;
localparam STATE_CMD_CONT  = STATE_CMD_START + RASCAS_DELAY;
localparam STATE_READ      = STATE_CMD_CONT + CAS_LATENCY + 3'd1;
localparam STATE_HIGHZ     = STATE_READ - 3'd1;

// Commands
localparam CMD_INHIBIT         = 4'b1111;
localparam CMD_NOP             = 4'b0111;
localparam CMD_ACTIVE          = 4'b0011;
localparam CMD_READ            = 4'b0101;
localparam CMD_WRITE           = 4'b0100;
localparam CMD_BURST_TERMINATE = 4'b0110;
localparam CMD_PRECHARGE       = 4'b0010;
localparam CMD_AUTO_REFRESH    = 4'b0001;
localparam CMD_LOAD_MODE       = 4'b0000;

reg [3:0] sd_cmd;

assign sd_cs  = sd_cmd[3];
assign sd_ras = sd_cmd[2];
assign sd_cas = sd_cmd[1];
assign sd_we  = sd_cmd[0];

assign sd_dqm = sd_addr[12:11];

// Reset counter
reg [4:0] reset;
always @(posedge clk) begin
    if (init) reset <= 5'h1f;
    else if ((stage == STATE_FIRST) && (reset != 0))
        reset <= reset - 5'd1;
end

reg  [1:0] mode;
reg [15:0] din_r;
reg  [2:0] stage;

always @(posedge clk) begin
    reg [12:0] addr_r;
    reg        old_sync;
    reg        old_oe;

    if (|stage) stage <= stage + 1'd1;

    old_sync <= sync;
    old_oe   <= oe;
    if (~old_sync && sync && autorefresh)  stage <= 1;
    if (refresh && stage == STATE_FIRST)   stage <= 1;
    if (~old_oe && oe && ~autorefresh)     stage <= 1;

    sd_cmd <= CMD_INHIBIT;
    sd_data_oe <= 1'b0;
    sd_data_out <= 16'h0000;

    if (reset != 0) begin
        // Initialization
        if (stage == STATE_CMD_START) begin
            if (reset == 13) begin
                sd_cmd <= CMD_PRECHARGE;
                sd_addr[10] <= 1'b1;
            end
            if (reset == 2) begin
                sd_cmd <= CMD_LOAD_MODE;
                sd_addr <= MODE;
            end
        end
        mode <= 0;
    end else begin
        // Normal operation
        if (stage == STATE_CMD_START) begin
            if (we || oe) begin
                mode <= {we, oe};
                sd_cmd  <= CMD_ACTIVE;
                sd_addr <= { 1'b0, addr[19:8] };
                sd_ba   <= addr[21:20];
                din_r   <= din;
                addr_r  <= { we ? ~ds : 2'b00, 2'b10, addr[22], addr[7:0] };
            end
            else if (autorefresh || refresh) begin
                sd_cmd <= CMD_AUTO_REFRESH;
                mode <= 0;
            end
        end

        // CAS phase
        if (stage == STATE_CMD_CONT && mode) begin
            sd_cmd  <= mode[1] ? CMD_WRITE : CMD_READ;
            sd_addr <= addr_r;
            if (mode[1]) begin
                sd_data_out <= din_r;
                sd_data_oe <= 1'b1;
            end
        end

        if (stage == STATE_HIGHZ) begin
            sd_addr[12:11] <= 2'b11;
            mode[1] <= 0;
        end

        if (stage == STATE_READ && mode) begin
            dout <= sd_data_in;
        end
    end
end

// Status signals for testbench
wire busy = (stage != 0);
wire ready = (reset == 0) && (stage == 0);

endmodule
