// Simplified FDC (Floppy Disk Controller) for Verilator Simulation
// Based on Intel 82077AA / NEC 765 compatible interface
//
// Provides essential FDC commands for testing:
// - Read Data, Write Data
// - Format Track
// - Seek, Recalibrate
// - Read ID, Sense Interrupt Status

`timescale 1ns / 1ps

module fdc_sim (
    input  wire        clk,
    input  wire        rst_n,

    // CPU I/O interface (ports 0x3F0-0x3F7)
    input  wire [2:0]  io_address,
    input  wire        io_read,
    input  wire        io_write,
    input  wire [7:0]  io_writedata,
    output reg  [7:0]  io_readdata,

    // DMA interface
    output reg         dma_req,
    input  wire        dma_ack,
    input  wire        dma_tc,      // Terminal count
    output reg  [7:0]  dma_writedata,
    input  wire [7:0]  dma_readdata,

    // Interrupt
    output reg         irq,

    // Disk interface (directly exposed for C++ model)
    output reg  [1:0]  request,     // 00=none, 01=read, 10=write, 11=format
    output reg  [7:0]  cylinder,
    output reg  [7:0]  head,
    output reg  [7:0]  sector,
    output reg  [7:0]  sector_count,
    output reg  [7:0]  drive,

    input  wire        disk_ready,
    input  wire [7:0]  disk_data_in,
    output reg  [7:0]  disk_data_out,
    output reg         disk_data_wr,
    output reg         disk_data_rd,
    input  wire        disk_error,

    // Drive status
    input  wire        disk_inserted,
    input  wire        disk_wp,
    input  wire        disk_changed,

    // Current position feedback
    input  wire [7:0]  current_cyl,

    // Debug
    output reg  [31:0] debug_state
);

// I/O Port addresses (offset from 0x3F0)
localparam PORT_SRA = 3'h0;   // Status Register A (read)
localparam PORT_SRB = 3'h1;   // Status Register B (read)
localparam PORT_DOR = 3'h2;   // Digital Output Register
localparam PORT_TDR = 3'h3;   // Tape Drive Register
localparam PORT_MSR = 3'h4;   // Main Status Register (read)
localparam PORT_DSR = 3'h4;   // Data Rate Select (write)
localparam PORT_DATA = 3'h5;  // Data Register (FIFO)
localparam PORT_DIR = 3'h7;   // Digital Input Register
localparam PORT_CCR = 3'h7;   // Configuration Control Register

// FDC Commands
localparam CMD_READ_DATA     = 5'h06;
localparam CMD_READ_DEL_DATA = 5'h0C;
localparam CMD_WRITE_DATA    = 5'h05;
localparam CMD_WRITE_DEL     = 5'h09;
localparam CMD_READ_TRACK    = 5'h02;
localparam CMD_FORMAT_TRACK  = 5'h0D;
localparam CMD_SCAN_EQUAL    = 5'h11;
localparam CMD_SCAN_LOW      = 5'h19;
localparam CMD_SCAN_HIGH     = 5'h1D;
localparam CMD_RECALIBRATE   = 5'h07;
localparam CMD_SENSE_INT     = 5'h08;
localparam CMD_SPECIFY       = 5'h03;
localparam CMD_SENSE_DRIVE   = 5'h04;
localparam CMD_SEEK          = 5'h0F;
localparam CMD_READ_ID       = 5'h0A;
localparam CMD_VERSION       = 5'h10;

// State machine
localparam S_IDLE          = 4'd0;
localparam S_READ_PARAMS   = 4'd1;
localparam S_EXECUTE       = 4'd2;
localparam S_READ_DATA     = 4'd3;
localparam S_WRITE_DATA    = 4'd4;
localparam S_RESULT        = 4'd5;
localparam S_WAIT_DMA      = 4'd6;
localparam S_FORMAT        = 4'd7;
localparam S_SEEK          = 4'd8;

reg [3:0] state;
reg [3:0] next_state;

// Registers
reg [7:0] dor;           // Digital Output Register
reg [7:0] dsr;           // Data Rate Select
reg [7:0] ccr;           // Configuration Control
reg       motor_on [0:1];
reg       dma_enable;
reg       reset_flag;

// Command processing
reg [7:0] cmd;
reg [4:0] cmd_type;
reg       mt_bit;        // Multi-track
reg       mfm_bit;       // MFM mode
reg       sk_bit;        // Skip deleted
reg [3:0] param_count;
reg [3:0] param_index;
reg [7:0] params [0:8];

// Result bytes
reg [3:0] result_count;
reg [3:0] result_index;
reg [7:0] results [0:6];

// Status registers
reg [7:0] st0, st1, st2;

// FIFO
reg [7:0] fifo [0:511];
reg [8:0] fifo_wr_ptr;
reg [8:0] fifo_rd_ptr;
reg       fifo_empty;
reg       fifo_full;

// Timing
reg [15:0] delay_counter;
reg        delay_active;

// Track sectors remaining
reg [7:0] sectors_remaining;
reg [8:0] bytes_remaining;

// Interrupt pending
reg       int_pending;
reg [7:0] int_st0;

// Main Status Register bits
wire msr_rqm = (state == S_IDLE || state == S_READ_PARAMS || state == S_RESULT);
wire msr_dio = (state == S_RESULT);
wire msr_ndm = 0;
wire msr_cb  = (state != S_IDLE);
wire [3:0] msr_db = {motor_on[1], motor_on[0], 2'b00};

wire [7:0] msr = {msr_rqm, msr_dio, msr_ndm, msr_cb, msr_db};

// I/O Read
always @(*) begin
    io_readdata = 8'hFF;

    case (io_address)
        PORT_SRA: io_readdata = 8'h00;
        PORT_SRB: io_readdata = 8'h00;
        PORT_DOR: io_readdata = dor;
        PORT_TDR: io_readdata = 8'h00;
        PORT_MSR: io_readdata = msr;
        PORT_DATA: begin
            if (state == S_RESULT && result_index < result_count) begin
                io_readdata = results[result_index];
            end else begin
                io_readdata = 8'h00;
            end
        end
        PORT_DIR: io_readdata = {disk_changed, 7'h00};
        default:  io_readdata = 8'hFF;
    endcase
end

// State machine
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= S_IDLE;
        dor <= 8'h00;
        dsr <= 8'h00;
        ccr <= 8'h00;
        motor_on[0] <= 0;
        motor_on[1] <= 0;
        dma_enable <= 0;
        reset_flag <= 0;

        cmd <= 0;
        cmd_type <= 0;
        param_count <= 0;
        param_index <= 0;
        result_count <= 0;
        result_index <= 0;

        st0 <= 8'h00;
        st1 <= 8'h00;
        st2 <= 8'h00;

        fifo_wr_ptr <= 0;
        fifo_rd_ptr <= 0;
        fifo_empty <= 1;
        fifo_full <= 0;

        delay_counter <= 0;
        delay_active <= 0;

        irq <= 0;
        dma_req <= 0;
        int_pending <= 0;

        request <= 2'b00;
        cylinder <= 0;
        head <= 0;
        sector <= 0;
        sector_count <= 0;
        drive <= 0;
        disk_data_out <= 0;
        disk_data_wr <= 0;
        disk_data_rd <= 0;

        debug_state <= 0;
    end else begin
        // Clear one-cycle signals
        disk_data_wr <= 0;
        disk_data_rd <= 0;

        // I/O Write handling
        if (io_write) begin
            case (io_address)
                PORT_DOR: begin
                    dor <= io_writedata;
                    motor_on[0] <= io_writedata[4];
                    motor_on[1] <= io_writedata[5];
                    dma_enable <= io_writedata[3];
                    reset_flag <= !io_writedata[2];
                end

                PORT_DSR: dsr <= io_writedata;
                PORT_CCR: ccr <= io_writedata;

                PORT_DATA: begin
                    if (state == S_IDLE) begin
                        // New command
                        cmd <= io_writedata;
                        cmd_type <= io_writedata[4:0];
                        mt_bit <= io_writedata[7];
                        mfm_bit <= io_writedata[6];
                        sk_bit <= io_writedata[5];
                        param_index <= 0;

                        // Determine parameter count
                        case (io_writedata[4:0])
                            CMD_READ_DATA, CMD_WRITE_DATA: param_count <= 8;
                            CMD_FORMAT_TRACK: param_count <= 5;
                            CMD_SEEK: param_count <= 2;
                            CMD_RECALIBRATE: param_count <= 1;
                            CMD_SPECIFY: param_count <= 2;
                            CMD_SENSE_DRIVE: param_count <= 1;
                            CMD_READ_ID: param_count <= 1;
                            CMD_SENSE_INT: param_count <= 0;
                            CMD_VERSION: param_count <= 0;
                            default: param_count <= 0;
                        endcase

                        if (io_writedata[4:0] == CMD_SENSE_INT ||
                            io_writedata[4:0] == CMD_VERSION) begin
                            state <= S_EXECUTE;
                        end else begin
                            state <= S_READ_PARAMS;
                        end
                    end
                    else if (state == S_READ_PARAMS) begin
                        params[param_index] <= io_writedata;
                        param_index <= param_index + 1;

                        if (param_index + 1 >= param_count) begin
                            state <= S_EXECUTE;
                        end
                    end
                end
            endcase
        end

        // I/O Read result handling
        if (io_read && io_address == PORT_DATA && state == S_RESULT) begin
            if (result_index + 1 >= result_count) begin
                state <= S_IDLE;
                irq <= 0;
            end else begin
                result_index <= result_index + 1;
            end
        end

        // State machine
        case (state)
            S_EXECUTE: begin
                case (cmd_type)
                    CMD_SENSE_INT: begin
                        if (int_pending) begin
                            results[0] <= int_st0;
                            results[1] <= current_cyl;
                            int_pending <= 0;
                        end else begin
                            results[0] <= 8'h80;  // Invalid
                            results[1] <= 0;
                        end
                        result_count <= 2;
                        result_index <= 0;
                        state <= S_RESULT;
                    end

                    CMD_VERSION: begin
                        results[0] <= 8'h90;  // 82077AA
                        result_count <= 1;
                        result_index <= 0;
                        state <= S_RESULT;
                    end

                    CMD_SPECIFY: begin
                        // Store timing parameters (ignored in simulation)
                        state <= S_IDLE;
                    end

                    CMD_SENSE_DRIVE: begin
                        drive <= params[0][1:0];
                        results[0] <= {disk_wp, 1'b0, 1'b1, params[0][2],
                                      2'b00, params[0][1:0]};
                        result_count <= 1;
                        result_index <= 0;
                        state <= S_RESULT;
                    end

                    CMD_RECALIBRATE: begin
                        drive <= params[0][1:0];
                        cylinder <= 0;
                        request <= 2'b01;  // Seek request
                        delay_counter <= 1000;  // Simulated delay
                        delay_active <= 1;
                        state <= S_SEEK;
                    end

                    CMD_SEEK: begin
                        drive <= params[0][1:0];
                        head <= params[0][2];
                        cylinder <= params[1];
                        request <= 2'b01;  // Seek request
                        delay_counter <= 500;
                        delay_active <= 1;
                        state <= S_SEEK;
                    end

                    CMD_READ_ID: begin
                        drive <= params[0][1:0];
                        head <= params[0][2];
                        // Return current position
                        results[0] <= {1'b0, 2'b00, 1'b0, 1'b0, 1'b0, params[0][1:0]};
                        results[1] <= 8'h00;
                        results[2] <= 8'h00;
                        results[3] <= current_cyl;
                        results[4] <= params[0][2];
                        results[5] <= 1;  // Sector 1
                        results[6] <= 2;  // Size code (512 bytes)
                        result_count <= 7;
                        result_index <= 0;
                        state <= S_RESULT;
                        irq <= 1;
                    end

                    CMD_READ_DATA: begin
                        drive <= params[0][1:0];
                        head <= params[0][2];
                        cylinder <= params[1];
                        sector <= params[3];
                        sector_count <= params[5];
                        sectors_remaining <= params[5];
                        bytes_remaining <= 512;
                        fifo_wr_ptr <= 0;
                        fifo_rd_ptr <= 0;
                        request <= 2'b01;  // Read
                        state <= S_READ_DATA;
                        dma_req <= dma_enable;
                    end

                    CMD_WRITE_DATA: begin
                        drive <= params[0][1:0];
                        head <= params[0][2];
                        cylinder <= params[1];
                        sector <= params[3];
                        sector_count <= params[5];
                        sectors_remaining <= params[5];
                        bytes_remaining <= 512;
                        fifo_wr_ptr <= 0;
                        fifo_rd_ptr <= 0;
                        request <= 2'b10;  // Write
                        state <= S_WRITE_DATA;
                        dma_req <= dma_enable;
                    end

                    CMD_FORMAT_TRACK: begin
                        drive <= params[0][1:0];
                        head <= params[0][2];
                        sector_count <= params[2];
                        request <= 2'b11;  // Format
                        state <= S_FORMAT;
                        dma_req <= dma_enable;
                    end

                    default: begin
                        state <= S_IDLE;
                    end
                endcase
            end

            S_SEEK: begin
                if (delay_active) begin
                    if (delay_counter > 0) begin
                        delay_counter <= delay_counter - 1;
                    end else begin
                        delay_active <= 0;
                        request <= 2'b00;
                        // Set interrupt
                        int_pending <= 1;
                        int_st0 <= {1'b0, 2'b00, 1'b0, 1'b1, 1'b0, drive[1:0]};
                        irq <= 1;
                        state <= S_IDLE;
                    end
                end
            end

            S_READ_DATA: begin
                if (disk_ready) begin
                    disk_data_rd <= 1;
                    fifo[fifo_wr_ptr] <= disk_data_in;
                    fifo_wr_ptr <= fifo_wr_ptr + 1;
                    bytes_remaining <= bytes_remaining - 1;

                    if (bytes_remaining == 1) begin
                        // Sector complete
                        sectors_remaining <= sectors_remaining - 1;
                        sector <= sector + 1;

                        if (sectors_remaining == 1 || dma_tc) begin
                            // Transfer complete
                            request <= 2'b00;
                            dma_req <= 0;
                            st0 <= {1'b0, 2'b00, 1'b0, 1'b0, head[0], drive[1:0]};
                            st1 <= 8'h00;
                            st2 <= 8'h00;
                            results[0] <= st0;
                            results[1] <= st1;
                            results[2] <= st2;
                            results[3] <= cylinder;
                            results[4] <= head;
                            results[5] <= sector;
                            results[6] <= 2;  // Size code
                            result_count <= 7;
                            result_index <= 0;
                            state <= S_RESULT;
                            irq <= 1;
                        end else begin
                            bytes_remaining <= 512;
                        end
                    end
                end

                // DMA transfer
                if (dma_ack && fifo_rd_ptr != fifo_wr_ptr) begin
                    dma_writedata <= fifo[fifo_rd_ptr];
                    fifo_rd_ptr <= fifo_rd_ptr + 1;
                end
            end

            S_WRITE_DATA: begin
                // DMA receive
                if (dma_ack) begin
                    fifo[fifo_wr_ptr] <= dma_readdata;
                    fifo_wr_ptr <= fifo_wr_ptr + 1;
                end

                // Write to disk
                if (fifo_rd_ptr != fifo_wr_ptr && disk_ready) begin
                    disk_data_out <= fifo[fifo_rd_ptr];
                    disk_data_wr <= 1;
                    fifo_rd_ptr <= fifo_rd_ptr + 1;
                    bytes_remaining <= bytes_remaining - 1;

                    if (bytes_remaining == 1) begin
                        sectors_remaining <= sectors_remaining - 1;
                        sector <= sector + 1;

                        if (sectors_remaining == 1 || dma_tc) begin
                            request <= 2'b00;
                            dma_req <= 0;
                            st0 <= {1'b0, 2'b00, 1'b0, 1'b0, head[0], drive[1:0]};
                            st1 <= 8'h00;
                            st2 <= 8'h00;
                            results[0] <= st0;
                            results[1] <= st1;
                            results[2] <= st2;
                            results[3] <= cylinder;
                            results[4] <= head;
                            results[5] <= sector;
                            results[6] <= 2;
                            result_count <= 7;
                            result_index <= 0;
                            state <= S_RESULT;
                            irq <= 1;
                        end else begin
                            bytes_remaining <= 512;
                        end
                    end
                end
            end

            S_FORMAT: begin
                if (disk_ready) begin
                    // Format complete
                    request <= 2'b00;
                    dma_req <= 0;
                    st0 <= {1'b0, 2'b00, 1'b0, 1'b0, head[0], drive[1:0]};
                    st1 <= 8'h00;
                    st2 <= 8'h00;
                    results[0] <= st0;
                    results[1] <= st1;
                    results[2] <= st2;
                    results[3] <= cylinder;
                    results[4] <= head;
                    results[5] <= 1;
                    results[6] <= 2;
                    result_count <= 7;
                    result_index <= 0;
                    state <= S_RESULT;
                    irq <= 1;
                end
            end

            default: ;
        endcase

        debug_state <= {24'h0, state, cmd_type[3:0]};
    end
end

endmodule
