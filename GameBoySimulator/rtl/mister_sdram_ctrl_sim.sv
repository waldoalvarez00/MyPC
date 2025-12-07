// Generic MiSTer SDRAM Controller for Verilator Simulation
// Supports both Native SDRAM interface and Avalon-MM interface
// Compatible with various MiSTer cores

module mister_sdram_ctrl_sim #(
    parameter SIZE_MB = 32
)(
    input  logic        clk,
    input  logic        reset,

    // ===============================================
    // Native SDRAM Interface (like SDRAMController.sv)
    // ===============================================
    // Host interface
    input  logic [25:1] h_addr,
    input  logic [15:0] h_wdata,
    output logic [15:0] h_rdata,
    input  logic        h_wr_en,
    input  logic [1:0]  h_bytesel,
    input  logic        h_access,
    output logic        h_compl,
    output logic        h_config_done,

    // Physical SDRAM signals (directly exposed for model)
    output logic        s_cs_n,
    output logic        s_ras_n,
    output logic        s_cas_n,
    output logic        s_we_n,
    output logic [1:0]  s_ba,
    output logic [12:0] s_addr,
    output logic [15:0] s_dq_out,
    input  logic [15:0] s_dq_in,
    output logic        s_dq_oe,
    output logic [1:0]  s_dqm,

    // ===============================================
    // Avalon-MM Interface (like HPS f2sdram)
    // ===============================================
    input  logic [28:0] av_address,
    input  logic [7:0]  av_burstcount,
    output logic        av_waitrequest,
    output logic [63:0] av_readdata,
    output logic        av_readdatavalid,
    input  logic        av_read,
    input  logic [63:0] av_writedata,
    input  logic [7:0]  av_byteenable,
    input  logic        av_write
);

    // ===============================================
    // Native SDRAM State Machine
    // ===============================================
    localparam STATE_RESET      = 4'h0;
    localparam STATE_RESET_PCH  = 4'h1;
    localparam STATE_RESET_REF1 = 4'h2;
    localparam STATE_RESET_REF2 = 4'h3;
    localparam STATE_MRS        = 4'h4;
    localparam STATE_IDLE       = 4'h5;
    localparam STATE_ACT        = 4'h6;
    localparam STATE_READ       = 4'h7;
    localparam STATE_WRITE      = 4'h8;
    localparam STATE_PCH        = 4'h9;
    localparam STATE_AUTOREF    = 4'hA;

    reg [3:0] state;
    reg [3:0] next_state;
    reg [15:0] timer;

    // Timing parameters (at 50 MHz)
    localparam tReset = 5000;
    localparam tRC    = 4;
    localparam tRP    = 2;
    localparam tMRD   = 2;
    localparam tRCD   = 2;
    localparam CAS    = 2;

    // Refresh timing
    reg [15:0] refresh_counter;
    localparam REFRESH_INTERVAL = 390;

    // Row tracking
    reg [12:0] open_row[0:3];
    reg [3:0]  row_is_open;

    // Address decomposition
    wire [1:0]  h_banksel;
    wire [12:0] h_rowsel;
    wire [12:0] col;

    generate
        if (SIZE_MB == 32) begin
            assign h_banksel = h_addr[11:10];
            assign h_rowsel  = h_addr[24:12];
            assign col       = {4'b0, h_addr[9:1]};
        end else begin
            assign h_banksel = h_addr[12:11];
            assign h_rowsel  = h_addr[25:13];
            assign col       = {3'b0, h_addr[10:1]};
        end
    endgenerate

    // Command generation
    reg [3:0] cmd;
    localparam CMD_NOP   = 4'b0111;
    localparam CMD_READ  = 4'b0101;
    localparam CMD_WRITE = 4'b0100;
    localparam CMD_ACT   = 4'b0011;
    localparam CMD_PRE   = 4'b0010;
    localparam CMD_REF   = 4'b0001;
    localparam CMD_MRS   = 4'b0000;

    assign s_cs_n  = cmd[3];
    assign s_ras_n = cmd[2];
    assign s_cas_n = cmd[1];
    assign s_we_n  = cmd[0];

    wire refresh_pending = (refresh_counter >= REFRESH_INTERVAL);

    // State machine - next state logic
    always_comb begin
        next_state = state;

        case (state)
            STATE_RESET:
                if (timer >= tReset) next_state = STATE_RESET_PCH;

            STATE_RESET_PCH:
                if (timer >= tRP) next_state = STATE_RESET_REF1;

            STATE_RESET_REF1:
                if (timer >= tRC) next_state = STATE_RESET_REF2;

            STATE_RESET_REF2:
                if (timer >= tRC) next_state = STATE_MRS;

            STATE_MRS:
                if (timer >= tMRD) next_state = STATE_IDLE;

            STATE_IDLE: begin
                if (!h_compl && refresh_pending)
                    next_state = STATE_PCH;
                else if (!h_compl && h_access) begin
                    if (row_is_open[h_banksel] && open_row[h_banksel] == h_rowsel)
                        next_state = h_wr_en ? STATE_WRITE : STATE_READ;
                    else if (row_is_open[h_banksel])
                        next_state = STATE_PCH;
                    else
                        next_state = STATE_ACT;
                end
            end

            STATE_ACT:
                if (timer >= tRCD) next_state = h_wr_en ? STATE_WRITE : STATE_READ;

            STATE_READ:
                if (timer >= CAS) next_state = STATE_IDLE;

            STATE_WRITE:
                if (timer >= tRP) next_state = STATE_IDLE;

            STATE_PCH:
                if (timer >= tRP) next_state = refresh_pending ? STATE_AUTOREF : STATE_IDLE;

            STATE_AUTOREF:
                if (timer >= tRC) next_state = STATE_IDLE;
        endcase

        if (reset) next_state = STATE_RESET;
    end

    // State machine registers
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= STATE_RESET;
            timer <= 0;
            cmd <= CMD_NOP;
            s_addr <= 0;
            s_ba <= 0;
            s_dq_oe <= 0;
            s_dq_out <= 0;
            s_dqm <= 2'b11;
            row_is_open <= 0;
            refresh_counter <= 0;
        end else begin
            timer <= (state != next_state) ? 0 : timer + 1;

            if (state == STATE_AUTOREF && timer == 0)
                refresh_counter <= 0;
            else
                refresh_counter <= refresh_counter + 1;

            state <= next_state;
            cmd <= CMD_NOP;
            s_dq_oe <= 0;

            if (state != next_state) begin
                case (next_state)
                    STATE_RESET_PCH: begin
                        cmd <= CMD_PRE;
                        s_addr <= 13'b0_0100_0000_0000;
                        s_ba <= 2'b00;
                    end

                    STATE_RESET_REF1, STATE_RESET_REF2:
                        cmd <= CMD_REF;

                    STATE_MRS: begin
                        cmd <= CMD_MRS;
                        s_ba <= 2'b00;
                        s_addr <= 13'b000_0_00_010_0_000;
                    end

                    STATE_ACT: begin
                        cmd <= CMD_ACT;
                        s_ba <= h_banksel;
                        s_addr <= h_rowsel;
                        open_row[h_banksel] <= h_rowsel;
                        row_is_open[h_banksel] <= 1;
                    end

                    STATE_READ: begin
                        cmd <= CMD_READ;
                        s_ba <= h_banksel;
                        s_addr <= col;
                    end

                    STATE_WRITE: begin
                        cmd <= CMD_WRITE;
                        s_ba <= h_banksel;
                        s_addr <= col;
                        s_dq_out <= h_wdata;
                        s_dq_oe <= 1;
                        s_dqm <= ~h_bytesel;
                    end

                    STATE_PCH: begin
                        cmd <= CMD_PRE;
                        if (refresh_pending) begin
                            s_addr <= 13'b0_0100_0000_0000;
                            row_is_open <= 0;
                        end else begin
                            s_addr <= 0;
                            row_is_open[h_banksel] <= 0;
                        end
                        s_ba <= h_banksel;
                    end

                    STATE_AUTOREF: begin
                        cmd <= CMD_REF;
                        row_is_open <= 0;
                    end

                    default: ;
                endcase
            end
        end
    end

    // Read data capture
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            h_rdata <= 0;
        else if (state == STATE_READ && timer == CAS)
            h_rdata <= s_dq_in;
    end

    // Completion signal
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            h_compl <= 0;
        else
            h_compl <= (state == STATE_READ && timer == CAS) ||
                       (state == STATE_WRITE && timer == tRP);
    end

    // Config done
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            h_config_done <= 0;
        else if (state == STATE_IDLE)
            h_config_done <= 1;
    end

    // ===============================================
    // Avalon-MM Interface
    // ===============================================
    reg [2:0] av_state;
    reg [7:0] av_burst_remaining;
    reg [28:0] av_current_addr;
    reg [3:0] av_latency;

    localparam AV_IDLE = 0;
    localparam AV_READ = 1;
    localparam AV_WRITE = 2;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            av_state <= AV_IDLE;
            av_waitrequest <= 0;
            av_readdatavalid <= 0;
            av_readdata <= 0;
            av_burst_remaining <= 0;
            av_current_addr <= 0;
            av_latency <= 0;
        end else begin
            av_readdatavalid <= 0;

            case (av_state)
                AV_IDLE: begin
                    if (av_read) begin
                        av_state <= AV_READ;
                        av_burst_remaining <= av_burstcount;
                        av_current_addr <= av_address;
                        av_latency <= CAS;
                        av_waitrequest <= 1;
                    end else if (av_write) begin
                        av_state <= AV_WRITE;
                        av_burst_remaining <= av_burstcount;
                        av_current_addr <= av_address;
                        av_waitrequest <= 1;
                    end
                end

                AV_READ: begin
                    av_waitrequest <= 0;
                    if (av_latency > 0) begin
                        av_latency <= av_latency - 1;
                    end else begin
                        av_readdatavalid <= 1;
                        av_burst_remaining <= av_burst_remaining - 1;
                        av_current_addr <= av_current_addr + 1;
                        if (av_burst_remaining == 1)
                            av_state <= AV_IDLE;
                    end
                end

                AV_WRITE: begin
                    av_waitrequest <= 0;
                    av_burst_remaining <= av_burst_remaining - 1;
                    av_current_addr <= av_current_addr + 1;
                    if (av_burst_remaining == 1)
                        av_state <= AV_IDLE;
                end
            endcase
        end
    end

endmodule
