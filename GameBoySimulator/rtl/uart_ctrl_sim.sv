// Simplified UART Controller for Verilator Simulation
// 16550-compatible interface for testing UART model
//
// Features:
// - Standard 16550 register set
// - TX/RX FIFOs
// - Loopback mode
// - Interrupt generation

module uart_ctrl_sim (
    input  logic        clk,
    input  logic        rst_n,

    // CPU I/O interface
    input  logic [2:0]  io_address,
    input  logic        io_read,
    input  logic        io_write,
    input  logic [7:0]  io_writedata,
    output logic [7:0]  io_readdata,

    // Serial interface
    input  logic [7:0]  rx_data_in,
    input  logic        rx_data_valid,
    output logic [7:0]  tx_data_out,
    output logic        tx_data_valid,

    // Modem signals (directly exposed for model)
    output logic        dtr_out,
    output logic        rts_out,
    input  logic        cts_in,
    input  logic        dsr_in,
    input  logic        dcd_in,
    input  logic        ri_in,

    // Interrupt
    output logic        irq
);

    // Registers
    reg [7:0]  ier;         // Interrupt Enable
    reg [7:0]  lcr;         // Line Control
    reg [7:0]  mcr;         // Modem Control
    reg [7:0]  lsr;         // Line Status
    reg [7:0]  msr;         // Modem Status
    reg [7:0]  scr;         // Scratch
    reg [15:0] divisor;     // Baud rate divisor

    // FIFO
    reg [7:0]  rx_fifo [0:15];
    reg [3:0]  rx_wr_ptr;
    reg [3:0]  rx_rd_ptr;
    reg [4:0]  rx_count;

    reg [7:0]  tx_fifo [0:15];
    reg [3:0]  tx_wr_ptr;
    reg [3:0]  tx_rd_ptr;
    reg [4:0]  tx_count;

    reg        fifo_enabled;
    reg [1:0]  rx_trigger;

    // Delayed RX read for pointer update
    reg        rx_read_pending;
    reg        io_read_prev;  // For edge detection

    // LSR bits
    localparam LSR_DR   = 0;    // Data ready
    localparam LSR_OE   = 1;    // Overrun error
    localparam LSR_THRE = 5;    // THR empty
    localparam LSR_TEMT = 6;    // Transmitter empty

    // LCR bits
    localparam LCR_DLAB = 7;    // Divisor latch access

    // MCR bits
    localparam MCR_DTR  = 0;
    localparam MCR_RTS  = 1;
    localparam MCR_OUT2 = 3;
    localparam MCR_LOOP = 4;

    // Modem outputs
    assign dtr_out = mcr[MCR_DTR];
    assign rts_out = mcr[MCR_RTS];

    // FIFO status
    wire rx_empty = (rx_count == 0);
    wire rx_full = (rx_count == 16);
    wire tx_empty = (tx_count == 0);
    wire tx_full = (tx_count == 16);

    // Main logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ier <= 8'h00;
            lcr <= 8'h00;
            mcr <= 8'h00;
            lsr <= 8'h60;  // THRE and TEMT
            msr <= 8'h00;
            scr <= 8'h00;
            divisor <= 16'h0001;

            rx_wr_ptr <= 4'h0;
            rx_rd_ptr <= 4'h0;
            rx_count <= 5'h0;
            tx_wr_ptr <= 4'h0;
            tx_rd_ptr <= 4'h0;
            tx_count <= 5'h0;

            fifo_enabled <= 1'b0;
            rx_trigger <= 2'b00;

            tx_data_valid <= 1'b0;
            rx_read_pending <= 1'b0;
            io_read_prev <= 1'b0;
        end else begin
            // Clear one-cycle signals
            tx_data_valid <= 1'b0;

            // Edge detection for io_read
            io_read_prev <= io_read;

            // Only set rx_read_pending on rising edge of io_read for RBR
            rx_read_pending <= io_read && !io_read_prev && !lcr[LCR_DLAB] && io_address == 3'h0;

            // Receive data
            if (rx_data_valid) begin
                if (mcr[MCR_LOOP]) begin
                    // Loopback - ignore external RX
                end else if (!rx_full) begin
                    rx_fifo[rx_wr_ptr] <= rx_data_in;
                    rx_wr_ptr <= rx_wr_ptr + 1;
                    rx_count <= rx_count + 1;
                    lsr[LSR_DR] <= 1'b1;
                end else begin
                    lsr[LSR_OE] <= 1'b1;
                end
            end

            // Transmit data from FIFO
            if (!tx_empty && !tx_data_valid) begin
                tx_data_out <= tx_fifo[tx_rd_ptr];
                tx_data_valid <= 1'b1;
                tx_rd_ptr <= tx_rd_ptr + 1;
                tx_count <= tx_count - 1;

                if (tx_count == 1) begin
                    lsr[LSR_THRE] <= 1'b1;
                    lsr[LSR_TEMT] <= 1'b1;
                end
            end

            // Update MSR
            if (mcr[MCR_LOOP]) begin
                // Loopback
                msr[7:4] <= {mcr[MCR_OUT2], mcr[0], mcr[MCR_RTS], mcr[MCR_DTR]};
            end else begin
                msr[7:4] <= {dcd_in, ri_in, dsr_in, cts_in};
            end

            // CPU write
            if (io_write) begin
                if (lcr[LCR_DLAB] && io_address == 3'h0) begin
                    divisor[7:0] <= io_writedata;
                end else if (lcr[LCR_DLAB] && io_address == 3'h1) begin
                    divisor[15:8] <= io_writedata;
                end else begin
                    case (io_address)
                        3'h0: begin  // THR
                            if (mcr[MCR_LOOP]) begin
                                // Loopback to RX
                                if (!rx_full) begin
                                    rx_fifo[rx_wr_ptr] <= io_writedata;
                                    rx_wr_ptr <= rx_wr_ptr + 1;
                                    rx_count <= rx_count + 1;
                                    lsr[LSR_DR] <= 1'b1;
                                end
                            end else if (!tx_full) begin
                                tx_fifo[tx_wr_ptr] <= io_writedata;
                                tx_wr_ptr <= tx_wr_ptr + 1;
                                tx_count <= tx_count + 1;
                                lsr[LSR_THRE] <= 1'b0;
                                lsr[LSR_TEMT] <= 1'b0;
                            end
                        end

                        3'h1: ier <= io_writedata & 8'h0F;

                        3'h2: begin  // FCR
                            fifo_enabled <= io_writedata[0];
                            if (io_writedata[1]) begin
                                // Clear RX FIFO
                                rx_wr_ptr <= 4'h0;
                                rx_rd_ptr <= 4'h0;
                                rx_count <= 5'h0;
                                lsr[LSR_DR] <= 1'b0;
                            end
                            if (io_writedata[2]) begin
                                // Clear TX FIFO
                                tx_wr_ptr <= 4'h0;
                                tx_rd_ptr <= 4'h0;
                                tx_count <= 5'h0;
                                lsr[LSR_THRE] <= 1'b1;
                                lsr[LSR_TEMT] <= 1'b1;
                            end
                            rx_trigger <= io_writedata[7:6];
                        end

                        3'h3: lcr <= io_writedata;
                        3'h4: mcr <= io_writedata & 8'h1F;
                        3'h7: scr <= io_writedata;
                        default: ;
                    endcase
                end
            end

            // CPU read side effects - delayed by one cycle
            if (io_read) begin
                case (io_address)
                    3'h5: begin  // LSR
                        lsr[LSR_OE] <= 1'b0;  // Clear error on read
                    end

                    3'h6: begin  // MSR
                        msr[3:0] <= 4'h0;  // Clear delta bits
                    end
                    default: ;
                endcase
            end

            // RBR read - update FIFO pointer delayed by one cycle
            // First cycle: latch data to io_readdata_reg
            // Second cycle: update pointer (using rx_read_pending)
            if (rx_read_pending && !rx_empty) begin
                rx_rd_ptr <= rx_rd_ptr + 1;
                rx_count <= rx_count - 1;
                if (rx_count == 1) begin
                    lsr[LSR_DR] <= 1'b0;
                end
            end
        end
    end

    // Read data mux - registered to avoid combinational loop with FIFO pointer
    reg [7:0] io_readdata_reg;
    assign io_readdata = io_readdata_reg;

    always_ff @(posedge clk) begin
        if (lcr[LCR_DLAB] && io_address == 3'h0) begin
            io_readdata_reg <= divisor[7:0];
        end else if (lcr[LCR_DLAB] && io_address == 3'h1) begin
            io_readdata_reg <= divisor[15:8];
        end else begin
            case (io_address)
                3'h0: io_readdata_reg <= rx_empty ? 8'h00 : rx_fifo[rx_rd_ptr];
                3'h1: io_readdata_reg <= ier;
                3'h2: io_readdata_reg <= {fifo_enabled ? 2'b11 : 2'b00, 4'b0001, ~|{ier & 8'h0F & {msr[3:0] != 0, lsr[4:1] != 0, lsr[LSR_DR], lsr[LSR_THRE]}}};
                3'h3: io_readdata_reg <= lcr;
                3'h4: io_readdata_reg <= mcr;
                3'h5: io_readdata_reg <= lsr;
                3'h6: io_readdata_reg <= msr;
                3'h7: io_readdata_reg <= scr;
                default: io_readdata_reg <= 8'h00;
            endcase
        end
    end

    // Interrupt generation
    wire int_rda = ier[0] && lsr[LSR_DR];
    wire int_thre = ier[1] && lsr[LSR_THRE];
    wire int_rls = ier[2] && |lsr[4:1];
    wire int_msi = ier[3] && |msr[3:0];

    assign irq = mcr[MCR_OUT2] && (int_rda || int_thre || int_rls || int_msi);

endmodule
