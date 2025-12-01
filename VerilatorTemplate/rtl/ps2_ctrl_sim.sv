// Simplified PS/2 Controller for Verilator Simulation
// Provides basic 8042-compatible PS/2 keyboard interface
//
// Based on ao486 PS/2 controller interface

`timescale 1ns / 1ps

module ps2_ctrl_sim (
    input  wire        clk,
    input  wire        rst_n,

    // CPU I/O interface
    input  wire [2:0]  io_address,
    input  wire        io_read,
    input  wire        io_write,
    input  wire [7:0]  io_writedata,
    output reg  [7:0]  io_readdata,

    // Interrupts
    output reg         irq_keyb,

    // Keyboard data interface (directly exposed for C++ model)
    input  wire [7:0]  kb_data_in,      // Data from keyboard
    input  wire        kb_data_valid,   // Keyboard data available
    output reg         kb_data_rd,      // Read strobe
    output reg  [7:0]  kb_cmd_out,      // Command to keyboard
    output reg         kb_cmd_valid,    // Command valid

    // Status
    output reg  [7:0]  status_reg
);

// I/O Port addresses
localparam PORT_DATA = 3'h0;     // 0x60
localparam PORT_STATUS = 3'h4;   // 0x64 (read)
localparam PORT_CMD = 3'h4;      // 0x64 (write)

// Status register bits
localparam ST_OBF  = 0;   // Output buffer full
localparam ST_IBF  = 1;   // Input buffer full
localparam ST_SYS  = 2;   // System flag
localparam ST_CMD  = 3;   // Command/data
localparam ST_INH  = 4;   // Inhibit switch
localparam ST_TTO  = 5;   // Transmit timeout
localparam ST_RTO  = 6;   // Receive timeout
localparam ST_PAR  = 7;   // Parity error

// Controller commands
localparam CMD_READ_CONFIG  = 8'h20;
localparam CMD_WRITE_CONFIG = 8'h60;
localparam CMD_DISABLE_KB   = 8'hAD;
localparam CMD_ENABLE_KB    = 8'hAE;
localparam CMD_TEST_KB      = 8'hAB;
localparam CMD_SELF_TEST    = 8'hAA;
localparam CMD_READ_OUTPUT  = 8'hD0;
localparam CMD_WRITE_OUTPUT = 8'hD1;

// State machine
localparam S_IDLE         = 3'd0;
localparam S_WAIT_DATA    = 3'd1;
localparam S_PROCESS_CMD  = 3'd2;
localparam S_SEND_KB      = 3'd3;

reg [2:0] state;

// Registers
reg [7:0] config_byte;
reg [7:0] output_buffer;
reg       output_buffer_full;
reg [7:0] input_buffer;
reg       input_buffer_full;
reg       awaiting_data;
reg [7:0] pending_cmd;

// Keyboard FIFO
reg [7:0] kb_fifo [0:15];
reg [3:0] kb_fifo_wr;
reg [3:0] kb_fifo_rd;
wire      kb_fifo_empty = (kb_fifo_wr == kb_fifo_rd);

// Build status register
always @(*) begin
    status_reg = 8'h00;
    status_reg[ST_OBF] = output_buffer_full;
    status_reg[ST_IBF] = input_buffer_full;
    status_reg[ST_SYS] = config_byte[2];
    status_reg[ST_CMD] = awaiting_data;
    status_reg[ST_INH] = 1'b0;
end

// I/O Read
always @(*) begin
    io_readdata = 8'hFF;

    case (io_address)
        PORT_DATA:   io_readdata = output_buffer;
        PORT_STATUS: io_readdata = status_reg;
        default:     io_readdata = 8'hFF;
    endcase
end

// Main logic
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= S_IDLE;
        config_byte <= 8'h47;  // Default: interrupts enabled, translation on
        output_buffer <= 8'h00;
        output_buffer_full <= 0;
        input_buffer <= 8'h00;
        input_buffer_full <= 0;
        awaiting_data <= 0;
        pending_cmd <= 0;
        irq_keyb <= 0;
        kb_data_rd <= 0;
        kb_cmd_out <= 0;
        kb_cmd_valid <= 0;
        kb_fifo_wr <= 0;
        kb_fifo_rd <= 0;
    end else begin
        // Clear one-cycle signals
        kb_data_rd <= 0;
        kb_cmd_valid <= 0;

        // Receive keyboard data into FIFO
        if (kb_data_valid) begin
            kb_fifo[kb_fifo_wr] <= kb_data_in;
            kb_fifo_wr <= kb_fifo_wr + 1;
        end

        // Transfer from FIFO to output buffer
        if (!output_buffer_full && !kb_fifo_empty) begin
            output_buffer <= kb_fifo[kb_fifo_rd];
            kb_fifo_rd <= kb_fifo_rd + 1;
            output_buffer_full <= 1;
            if (config_byte[0]) begin  // Interrupt enabled
                irq_keyb <= 1;
            end
        end

        // Handle I/O reads
        if (io_read && io_address == PORT_DATA) begin
            output_buffer_full <= 0;
            irq_keyb <= 0;
        end

        // Handle I/O writes
        if (io_write) begin
            case (io_address)
                PORT_DATA: begin
                    if (awaiting_data) begin
                        // Parameter for previous command
                        case (pending_cmd)
                            CMD_WRITE_CONFIG: begin
                                config_byte <= io_writedata;
                                awaiting_data <= 0;
                            end
                            CMD_WRITE_OUTPUT: begin
                                // Output port write (A20, reset, etc.)
                                awaiting_data <= 0;
                            end
                            default: begin
                                // Send to keyboard
                                kb_cmd_out <= io_writedata;
                                kb_cmd_valid <= 1;
                                awaiting_data <= 0;
                            end
                        endcase
                    end else begin
                        // Send to keyboard
                        kb_cmd_out <= io_writedata;
                        kb_cmd_valid <= 1;
                    end
                end

                PORT_CMD: begin
                    // Controller command
                    case (io_writedata)
                        CMD_READ_CONFIG: begin
                            output_buffer <= config_byte;
                            output_buffer_full <= 1;
                        end

                        CMD_WRITE_CONFIG: begin
                            awaiting_data <= 1;
                            pending_cmd <= io_writedata;
                        end

                        CMD_DISABLE_KB: begin
                            config_byte[4] <= 1;  // Disable keyboard
                        end

                        CMD_ENABLE_KB: begin
                            config_byte[4] <= 0;  // Enable keyboard
                        end

                        CMD_TEST_KB: begin
                            output_buffer <= 8'h00;  // Test passed
                            output_buffer_full <= 1;
                        end

                        CMD_SELF_TEST: begin
                            output_buffer <= 8'h55;  // Self-test passed
                            output_buffer_full <= 1;
                        end

                        CMD_READ_OUTPUT: begin
                            output_buffer <= 8'h00;
                            output_buffer_full <= 1;
                        end

                        CMD_WRITE_OUTPUT: begin
                            awaiting_data <= 1;
                            pending_cmd <= io_writedata;
                        end

                        default: begin
                            if (io_writedata >= 8'h60 && io_writedata <= 8'h7F) begin
                                // Write to internal RAM (not implemented)
                            end
                        end
                    endcase
                end
            endcase
        end
    end
end

endmodule
