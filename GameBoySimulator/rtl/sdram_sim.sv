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
    output reg [15:0] dout
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
    reg [3:0] cycle;
    reg [23:0] addr_r;
    reg [15:0] din_r;
    reg [1:0] ds_r;
    reg we_r;
    reg oe_r;

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

    initial begin
        state = IDLE;
        cycle = 0;
        cmd = CMD_NOP;
        sd_ba = 2'b00;
        sd_addr = 13'h0;
        sd_dqm = 2'b11;
        dout = 16'h0;
        sd_data = 16'h0;
        data_write = 0;
    end

    always @(posedge clk) begin
        if (init) begin
            state <= IDLE;
            cycle <= 0;
            cmd <= CMD_NOP;
            sd_dqm <= 2'b11;
            data_write <= 0;
        end
        else if (sync) begin
            // Default to NOP
            cmd <= CMD_NOP;
            sd_dqm <= 2'b11;
            data_write <= 0;

            case (state)
                IDLE: begin
                    if (we | oe) begin
                        // Latch inputs
                        addr_r <= addr;
                        din_r <= din;
                        ds_r <= ds;
                        we_r <= we;
                        oe_r <= oe;

                        // Start access - activate row
                        cmd <= CMD_ACTIVE;
                        sd_ba <= addr[23:22];
                        sd_addr <= addr[22:10];  // Row address
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
                    cycle <= cycle + 1;
                    if (cycle >= 1) begin
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
                    cycle <= cycle + 1;
                    if (cycle >= 2) begin
                        // Data available from SDRAM (C++ model provides it)
                        // dout is updated by external connection
                        state <= PRECHARGE;
                        cycle <= 0;
                    end
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

endmodule
