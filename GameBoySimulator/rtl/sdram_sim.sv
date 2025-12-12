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

    // --------------------------------------------------------------------
    // Timing parameters (simulation)
    // --------------------------------------------------------------------
    // This stub drives an external C++ SDRAM model which provides the actual
    // storage and CAS-latency behavior. However, if we immediately return to
    // IDLE and re-issue READ commands while `oe` stays asserted, the C++ model
    // keeps resetting its internal pending counter and the read never completes.
    //
    // Model the "bus busy" time in the controller so a READ is not restarted
	    // until at least CAS_LATENCY clocks have elapsed.
	    parameter integer CAS_LATENCY = 2;
	    parameter integer WRITE_LATENCY = 2;
	    parameter integer TRCD = 2;
	    localparam [2:0] CAS_LATENCY_BITS = CAS_LATENCY;

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
    // Registered dout value.
    //
    // NOTE: In the Verilator harness, `sd_data_in` is updated by the C++ SDRAM
    // model after the rising-edge eval and before the falling-edge eval.
    // Latch on the falling edge so the CPU sees the updated read data on the
    // next rising edge (avoids stale opcode/imm sampling when CAS latency > 0).
    reg [15:0] dout_r;

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

    assign dout = dout_r;

    // Debug signals (exposed for C++ testbench)
    reg [2:0] dbg_state /*verilator public_flat*/;
    reg dbg_oe_pending /*verilator public_flat*/;
    reg dbg_we_pending /*verilator public_flat*/;
    reg [15:0] dbg_dout_r /*verilator public_flat*/;
    reg dbg_oe_r /*verilator public_flat*/;

	    // Only accept one request per asserted oe/we level. This prevents repeated
	    // reads/writes when the CPU holds the bus strobes active across WAIT stretch.
	    reg [23:0] last_started_addr;
	    reg        last_started_is_write;
	    reg        last_started_valid;

	    // Model a minimal init sequence by issuing an MRS once after `init` deasserts
	    // so the C++ SDRAM model picks up CAS latency / burst length.
	    reg mode_done;

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
	        last_started_addr = 24'h0;
	        last_started_is_write = 1'b0;
	        last_started_valid = 1'b0;
	        mode_done = 1'b0;
	    end

    always @(posedge clk) begin
        // Update debug signals
        dbg_state <= state;
        dbg_oe_pending <= oe_pending;
        dbg_we_pending <= we_pending;
        dbg_dout_r <= dout_r;
        dbg_oe_r <= oe_r;

        // NOTE: Read data latching happens on negedge (see below).

	        if (init) begin
	            state <= IDLE;
	            cycle <= 0;
	            cmd <= CMD_NOP;
	            sd_dqm <= 2'b11;
	            data_write <= 0;
	            oe_pending <= 0;
	            we_pending <= 0;
	            oe_r <= 1'b0;
	            we_r <= 1'b0;
	            last_started_addr <= 24'h0;
	            last_started_is_write <= 1'b0;
	            last_started_valid <= 1'b0;
	            mode_done <= 1'b0;
	        end
	        else begin
            // CRITICAL: Default cmd to NOP on EVERY clock cycle
            // Commands are only issued on sync edges, but C++ model samples every cycle
            // Without this, stale commands are processed multiple times
            cmd <= CMD_NOP;

	            // Request latching:
	            // The GameBoy CPU can keep `oe` asserted while changing the address for
	            // back-to-back byte reads (RD_n stays low across stretched WAIT states).
	            // Only accept a new request when the address changes vs the last started
	            // request, otherwise we can either (a) restart reads forever or (b) never
	            // issue the next sequential read.
	            if (!oe && !we) begin
	                last_started_valid <= 1'b0;
	            end else if (!oe_pending && !we_pending) begin
	                if (oe && (!last_started_valid || last_started_is_write || (addr != last_started_addr))) begin
	                    oe_pending <= 1'b1;
	                    addr_pending <= addr;
	                    ds_pending <= ds;
	                end else if (we && (!last_started_valid || !last_started_is_write || (addr != last_started_addr))) begin
	                    we_pending <= 1'b1;
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
	                        // Issue a MODE REGISTER SET once after init deassert so the
	                        // external SDRAM model uses the requested CAS latency.
	                        if (!mode_done) begin
	                            cmd <= CMD_MODE;
	                            sd_ba <= 2'b00;
	                            // C++ model: cas_latency=(addr>>4)&7, burst_length=1<<(addr&7)
	                            sd_addr <= {6'b0, CAS_LATENCY_BITS, 4'b0000}; // BL=1, CAS=CAS_LATENCY
	                            mode_done <= 1'b1;
	                        end
	                        // Only start an access when we have a latched request.
	                        else if (we_pending | oe_pending) begin
	                            addr_r <= addr_pending;
	                            din_r <= din_pending;
	                            ds_r <= ds_pending;
	                            we_r <= we_pending;
	                            oe_r <= oe_pending;

	                            last_started_addr <= addr_pending;
	                            last_started_is_write <= we_pending;
	                            last_started_valid <= 1'b1;

	                            oe_pending <= 1'b0;
	                            we_pending <= 1'b0;

                            // Start access - activate row
	                            cmd <= CMD_ACTIVE;
	                            sd_ba <= addr_pending[23:22];
	                            sd_addr <= addr_pending[22:10];  // Row address
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
	                        // tRCD: wait TRCD cycles after ACT before issuing READ/WRITE.
	                        if (cycle + 1 < TRCD) begin
	                            cycle <= cycle + 1;
	                        end else begin
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
	                    end

                    READ: begin
                        // Hold the controller busy for CAS_LATENCY clocks after READ.
                        // This prevents restarting the read before the C++ model produces data.
                        if (cycle + 1 >= CAS_LATENCY) begin
                            state <= PRECHARGE;
                            cycle <= 0;
                        end else begin
                            cycle <= cycle + 1;
                        end
                    end

                    WRITE: begin
                        if (cycle + 1 >= WRITE_LATENCY) begin
                            state <= PRECHARGE;
                            cycle <= 0;
                        end else begin
                            cycle <= cycle + 1;
                        end
                    end

	                    PRECHARGE: begin
	                        cmd <= CMD_PRECHARGE;
	                        sd_addr <= 13'h400;  // Precharge all banks (A10=1)
	                        state <= IDLE;
	                        // Clear the current request qualifier once the command sequence completes.
	                        oe_r <= 1'b0;
	                        we_r <= 1'b0;
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

    // Latch read data on the falling edge so the C++ SDRAM model has had a chance
    // to update `sd_data_in` for the current cycle (including CAS latency).
    always @(negedge clk) begin
        if (init) begin
            dout_r <= 16'h0000;
        end else if (oe_r) begin
            dout_r <= sd_data_in;
        end
    end

endmodule
