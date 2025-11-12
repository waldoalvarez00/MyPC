// Copyright 2025, Waldo Alvarez
// FPU I/O Port Interface
//
// Provides I/O port-based data transfer between CPU and FPU
// for register operands (not memory operands)
//
// I/O Port Map (all 16-bit ports):
//   0xF8: Data Word 0 (bits 15:0)   - Low word
//   0xFA: Data Word 1 (bits 31:16)
//   0xFC: Data Word 2 (bits 47:32)
//   0xFE: Data Word 3 (bits 63:48)
//   0xF0: Data Word 4 (bits 79:64)  - High word (extended precision)
//   0xF2: Control/Status register
//         Bits [2:0]: Data size (0=16bit, 1=32bit, 2=64bit, 3=80bit)
//         Bit [8]: Transfer direction (0=CPU->FPU, 1=FPU->CPU)
//         Bit [9]: Data ready flag
//         Bit [10]: Transfer complete
//   0xF4: Command register
//         Write 1: Initiate transfer (auto-cleared)

`default_nettype none

module FPU_IO_Port(
    input wire clk,
    input wire reset,

    // CPU I/O Bus Interface
    input wire [15:0] io_addr,
    input wire [15:0] io_data_out,    // Data from CPU
    output reg [15:0] io_data_in,     // Data to CPU
    input wire io_access,
    output reg io_ack,
    input wire io_wr_en,

    // FPU Data Transfer Interface
    output reg fpu_data_write,
    output reg fpu_data_read,
    output reg [2:0] fpu_data_size,
    output reg [79:0] fpu_data_out,   // To FPU
    input wire [79:0] fpu_data_in,    // From FPU
    input wire fpu_data_ready
);

    // I/O Port addresses
    localparam ADDR_DATA_W0 = 16'hFFF8;
    localparam ADDR_DATA_W1 = 16'hFFFA;
    localparam ADDR_DATA_W2 = 16'hFFFC;
    localparam ADDR_DATA_W3 = 16'hFFFE;
    localparam ADDR_DATA_W4 = 16'hFFF0;
    localparam ADDR_CONTROL = 16'hFFF2;
    localparam ADDR_COMMAND = 16'hFFF4;

    // Internal data buffer (80-bit)
    reg [79:0] data_buffer;

    // Control register
    reg [2:0] data_size_reg;
    reg transfer_direction;  // 0=CPU->FPU, 1=FPU->CPU
    reg transfer_complete;

    // Detect I/O port access
    wire is_fpu_io_access = io_access && (
        io_addr == ADDR_DATA_W0 ||
        io_addr == ADDR_DATA_W1 ||
        io_addr == ADDR_DATA_W2 ||
        io_addr == ADDR_DATA_W3 ||
        io_addr == ADDR_DATA_W4 ||
        io_addr == ADDR_CONTROL ||
        io_addr == ADDR_COMMAND
    );

    // Transfer state machine
    typedef enum logic [1:0] {
        IDLE,
        WRITE_WAIT,
        READ_WAIT,
        COMPLETE
    } state_t;

    state_t state;

    // Handle I/O reads
    always_comb begin
        io_data_in = 16'h0000;

        if (is_fpu_io_access && !io_wr_en) begin
            case (io_addr)
                ADDR_DATA_W0: io_data_in = data_buffer[15:0];
                ADDR_DATA_W1: io_data_in = data_buffer[31:16];
                ADDR_DATA_W2: io_data_in = data_buffer[47:32];
                ADDR_DATA_W3: io_data_in = data_buffer[63:48];
                ADDR_DATA_W4: io_data_in = data_buffer[79:64];
                ADDR_CONTROL: io_data_in = {5'b0, transfer_complete, fpu_data_ready, transfer_direction, 5'b0, data_size_reg};
                ADDR_COMMAND: io_data_in = 16'h0000;
                default: io_data_in = 16'h0000;
            endcase
        end
    end

    // Handle I/O writes and transfer state machine
    always_ff @(posedge clk) begin
        if (reset) begin
            data_buffer <= 80'h0;
            data_size_reg <= 3'b0;
            transfer_direction <= 1'b0;
            transfer_complete <= 1'b0;
            fpu_data_write <= 1'b0;
            fpu_data_read <= 1'b0;
            fpu_data_size <= 3'b0;
            fpu_data_out <= 80'h0;
            io_ack <= 1'b0;
            state <= IDLE;
        end else begin
            // Default: clear single-cycle signals
            fpu_data_write <= 1'b0;
            fpu_data_read <= 1'b0;
            io_ack <= 1'b0;

            // I/O port writes
            if (is_fpu_io_access && io_wr_en) begin
                io_ack <= 1'b1;

                case (io_addr)
                    ADDR_DATA_W0: data_buffer[15:0] <= io_data_out;
                    ADDR_DATA_W1: data_buffer[31:16] <= io_data_out;
                    ADDR_DATA_W2: data_buffer[47:32] <= io_data_out;
                    ADDR_DATA_W3: data_buffer[63:48] <= io_data_out;
                    ADDR_DATA_W4: data_buffer[79:64] <= io_data_out;

                    ADDR_CONTROL: begin
                        data_size_reg <= io_data_out[2:0];
                        transfer_direction <= io_data_out[8];
                    end

                    ADDR_COMMAND: begin
                        if (io_data_out[0]) begin
                            // Initiate transfer
                            transfer_complete <= 1'b0;

                            if (!transfer_direction) begin
                                // CPU -> FPU write
                                fpu_data_out <= data_buffer;
                                fpu_data_size <= data_size_reg;
                                fpu_data_write <= 1'b1;
                                state <= WRITE_WAIT;
                            end else begin
                                // FPU -> CPU read
                                fpu_data_size <= data_size_reg;
                                fpu_data_read <= 1'b1;
                                state <= READ_WAIT;
                            end
                        end
                    end
                endcase
            end

            // I/O port reads
            if (is_fpu_io_access && !io_wr_en) begin
                io_ack <= 1'b1;
            end

            // Transfer state machine
            case (state)
                IDLE: begin
                    transfer_complete <= 1'b0;
                end

                WRITE_WAIT: begin
                    // Wait for FPU to accept data
                    if (fpu_data_ready) begin
                        transfer_complete <= 1'b1;
                        state <= COMPLETE;
                    end
                end

                READ_WAIT: begin
                    // Wait for FPU to provide data
                    if (fpu_data_ready) begin
                        data_buffer <= fpu_data_in;
                        transfer_complete <= 1'b1;
                        state <= COMPLETE;
                    end
                end

                COMPLETE: begin
                    state <= IDLE;
                end
            endcase
        end
    end

endmodule

`default_nettype wire
