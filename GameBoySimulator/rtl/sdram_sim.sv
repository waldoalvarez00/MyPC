//
// SDRAM Controller Simulation Stub
// Non-tristate version for Verilator simulation
//
// This is a simplified SDRAM controller that exposes separate
// data input and output signals instead of tristate sd_data.
//

module sdram (
    // Interface to SDRAM chip
    output reg [15:0] sd_data,      // Output to SDRAM (directly exposed to C++ model)
    input      [15:0] sd_data_in,   // Input from SDRAM (read data from C++ model)
    output reg [12:0] sd_addr,
    output reg [1:0]  sd_dqm,
    output reg [1:0]  sd_ba,
    output reg        sd_cs,
    output reg        sd_we,
    output reg        sd_ras,
    output reg        sd_cas,
    output            sd_clk,

    // System interface
    input             clk,
    input             sync,
    input             init,

    // CPU interface
    input  [15:0]     din,
    input  [23:0]     addr,
    input  [1:0]      ds,
    input             we,
    input             oe,
    input             autorefresh,
    input             refresh,
    output     [15:0] dout /*verilator public_flat*/
);

    // SDRAM clock output (directly from system clock for simulation)
    assign sd_clk = clk;

    // State machine states
    localparam IDLE     = 3'd0;
    localparam ACTIVATE = 3'd1;
    localparam READ     = 3'd2;
    localparam WRITE    = 3'd3;
    localparam REFRESH  = 3'd4;
    localparam PRECHARGE = 3'd5;

    reg [2:0] state;
    reg [3:0] cycle /*verilator public_flat*/;
    reg [23:0] addr_r;
    reg [15:0] din_r;
    reg [1:0] ds_r;
    reg we_r;
    reg oe_r;
    reg [15:0] dout_r;  // Registered dout value

    // Request latching - capture oe/we when they go high, process on next sync
    // This fixes timing issues where oe/we may only be high between sync pulses
    reg oe_pending;
    reg we_pending;
    reg [23:0] addr_pending;
    reg [15:0] din_pending;
    reg [1:0] ds_pending;

    // Row and column extraction
    wire [12:0] row = addr_r[22:10];
    wire [9:0]  col = addr_r[9:0];
    wire [1:0]  bank = addr_r[23:22];

    // Command encoding
    localparam CMD_NOP       = 4'b0111;
    localparam CMD_ACTIVE    = 4'b0011;
    localparam CMD_READ      = 4'b0101;
    localparam CMD_WRITE     = 4'b0100;
    localparam CMD_PRECHARGE = 4'b0010;
    localparam CMD_REFRESH   = 4'b0001;
    localparam CMD_MODE      = 4'b0000;

    reg [3:0] cmd;

    // Output command signals
    always @(*) begin
        sd_cs  = cmd[3];
        sd_ras = cmd[2];
        sd_cas = cmd[1];
        sd_we  = cmd[0];
    end

    // For simulation, use simplified timing
    // Real SDRAM controller has complex timing requirements
    // This stub assumes instantaneous responses (C++ model handles timing)

    reg [15:0] sd_data_out;  // Data to write to SDRAM
    reg        data_write;   // Writing data

    // Output captured data from dout_r
    // In zero-latency simulation mode, data is captured early (line 140-142) when it
    // briefly appears on sd_data_in. We must use the registered dout_r value, not
    // sd_data_in directly, because sd_data_in is only valid for 1 cycle.
    assign dout = dout_r;

    // Debug signals (exposed for C++ testbench)
    reg [2:0] dbg_state /*verilator public_flat*/;
    reg dbg_oe_pending /*verilator public_flat*/;
    reg dbg_we_pending /*verilator public_flat*/;
    reg [15:0] dbg_dout_r /*verilator public_flat*/;
    reg dbg_oe_r /*verilator public_flat*/;

    initial begin
        state = IDLE;
        cycle = 0;
        cmd = CMD_NOP;
        sd_ba = 2'b00;
        sd_addr = 13'h0;
        sd_dqm = 2'b11;
        dout_r = 16'h0;
        sd_data = 16'h0;
        data_write = 0;
        oe_pending = 0;
        we_pending = 0;
        addr_pending = 24'h0;
        din_pending = 16'h0;
        ds_pending = 2'b00;
        dbg_state = IDLE;
        dbg_oe_pending = 0;
        dbg_we_pending = 0;
    end

    always @(posedge clk) begin
        // Update debug signals
        dbg_state <= state;
        dbg_oe_pending <= oe_pending;
        dbg_we_pending <= we_pending;
        dbg_dout_r <= dout_r;
        dbg_oe_r <= oe_r;

        // CRITICAL FIX: Capture read data immediately when it becomes valid
        // In zero-latency simulation mode, the C++ SDRAM model processes commands
        // and returns data BETWEEN Verilog clock edges. The data appears on sd_data_in
        // after CMD_READ is issued, but the Verilog code executing at posedge clk sees
        // it only on the NEXT cycle. To capture transient data that appears for just
        // 1 cycle, we must latch sd_data_in whenever it's non-zero during a read.
        // This fixes the timing mismatch where data briefly appears at cycle N but
        // is gone by the time we would normally capture it in READ state at cycle N+1.
        if (!init && oe_r && sd_data_in != 16'h0000) begin
            dout_r <= sd_data_in;
        end

        if (init) begin
            state <= IDLE;
            cycle <= 0;
            cmd <= CMD_NOP;
            sd_dqm <= 2'b11;
            data_write <= 0;
            oe_pending <= 0;
            we_pending <= 0;
        end
        else begin
            // CRITICAL: Default cmd to NOP on EVERY clock cycle
            // Commands are only issued on sync edges, but C++ model samples every cycle
            // Without this, stale commands are processed multiple times
            cmd <= CMD_NOP;

            // Request latching: capture requests on ANY clock edge (regardless of state)
            // This ensures we don't miss oe/we that happen during REFRESH or other states
            // The pending flags persist until processed in IDLE state on a sync edge
            if (!oe_pending && !we_pending) begin
                if (oe) begin
                    oe_pending <= 1;
                    addr_pending <= addr;
                    ds_pending <= ds;
                end
                else if (we) begin
                    we_pending <= 1;
                    addr_pending <= addr;
                    din_pending <= din;
                    ds_pending <= ds;
                end
            end

            // State machine only advances on sync edges
            if (sync) begin
                // Default to NOP
                cmd <= CMD_NOP;
                sd_dqm <= 2'b11;
                data_write <= 0;

                case (state)
                    IDLE: begin
                        // Check pending requests (latched) OR current signals
                        if (we_pending | we | oe_pending | oe) begin
                            // Use pending values if available, otherwise use current
                            if (we_pending | oe_pending) begin
                                addr_r <= addr_pending;
                                din_r <= din_pending;
                                ds_r <= ds_pending;
                                we_r <= we_pending;
                                oe_r <= oe_pending;
                            end
                            else begin
                                addr_r <= addr;
                                din_r <= din;
                                ds_r <= ds;
                                we_r <= we;
                                oe_r <= oe;
                            end

                            // Clear pending flags
                            oe_pending <= 0;
                            we_pending <= 0;

                            // Start access - activate row
                            cmd <= CMD_ACTIVE;
                            if (we_pending | oe_pending) begin
                                sd_ba <= addr_pending[23:22];
                                sd_addr <= addr_pending[22:10];  // Row address
                            end
                            else begin
                                sd_ba <= addr[23:22];
                                sd_addr <= addr[22:10];  // Row address
                            end
                            state <= ACTIVATE;
                            cycle <= 0;
                        end
                        else if (refresh | autorefresh) begin
                            cmd <= CMD_REFRESH;
                            state <= REFRESH;
                            cycle <= 0;
                        end
                    end

                    ACTIVATE: begin
                        // Zero-latency simulation mode - proceed immediately
                        if (we_r) begin
                            // Write command
                            cmd <= CMD_WRITE;
                            sd_ba <= addr_r[23:22];
                            sd_addr <= {3'b000, addr_r[9:0]};  // Column address
                            sd_dqm <= ~ds_r;
                            sd_data <= din_r;
                            data_write <= 1;
                            state <= WRITE;
                            cycle <= 0;
                        end
                        else begin
                            // Read command
                            cmd <= CMD_READ;
                            sd_ba <= addr_r[23:22];
                            sd_addr <= {3'b000, addr_r[9:0]};  // Column address
                            sd_dqm <= 2'b00;
                            state <= READ;
                            cycle <= 0;
                        end
                    end

                    READ: begin
                        // Zero-latency simulation mode - data already captured above (line 140-142)
                        // The fix at line 140 captures sd_data_in as soon as it becomes valid,
                        // which happens BEFORE we enter this READ state. Don't overwrite dout_r
                        // here because sd_data_in is already gone (back to 0x0000) by now.
                        // OLD CODE (removed): dout_r <= sd_data_in;
                        state <= PRECHARGE;
                        cycle <= 0;
                    end

                    WRITE: begin
                        cycle <= cycle + 1;
                        if (cycle >= 1) begin
                            state <= PRECHARGE;
                            cycle <= 0;
                        end
                    end

                    PRECHARGE: begin
                        cmd <= CMD_PRECHARGE;
                        sd_addr[10] <= 1'b1;  // Precharge all banks
                        state <= IDLE;
                    end

                    REFRESH: begin
                        cycle <= cycle + 1;
                        if (cycle >= 3) begin
                            state <= IDLE;
                        end
                    end

                    default: state <= IDLE;
                endcase
            end
        end
    end

endmodule
