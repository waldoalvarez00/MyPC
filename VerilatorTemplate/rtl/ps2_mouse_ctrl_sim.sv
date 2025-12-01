// Simplified PS/2 Mouse Controller for Verilator Simulation
// Based on 8042 PS/2 controller auxiliary port interface
//
// This is a simplified version for testing the mouse model.
// It provides a basic 8042-like interface at ports 0x60/0x64.

module ps2_mouse_ctrl_sim (
    input  logic        clk,
    input  logic        rst_n,

    // CPU I/O interface
    input  logic [7:0]  io_address,     // 0x00=data, 0x04=status/cmd
    input  logic        io_read,
    input  logic        io_write,
    input  logic [7:0]  io_writedata,
    output logic [7:0]  io_readdata,

    // Mouse data interface (directly from model)
    input  logic [7:0]  mouse_data_in,
    input  logic        mouse_data_valid,

    // Command to mouse
    output logic [7:0]  mouse_cmd_out,
    output logic        mouse_cmd_valid,

    // Interrupt
    output logic        irq_mouse
);

    // Status register bits
    localparam STATUS_OBF = 0;    // Output buffer full
    localparam STATUS_IBF = 1;    // Input buffer full
    localparam STATUS_SYS = 2;    // System flag
    localparam STATUS_A2  = 3;    // Address line A2
    localparam STATUS_INH = 4;    // Inhibit flag
    localparam STATUS_MOBF = 5;   // Mouse output buffer full
    localparam STATUS_TO  = 6;    // Timeout
    localparam STATUS_PE  = 7;    // Parity error

    // Controller commands
    localparam CMD_READ_CONFIG = 8'h20;
    localparam CMD_WRITE_CONFIG = 8'h60;
    localparam CMD_DISABLE_MOUSE = 8'hA7;
    localparam CMD_ENABLE_MOUSE = 8'hA8;
    localparam CMD_TEST_MOUSE = 8'hA9;
    localparam CMD_SELF_TEST = 8'hAA;
    localparam CMD_WRITE_MOUSE = 8'hD4;

    // Configuration byte bits
    localparam CFG_MOUSE_INT = 1;   // Mouse interrupt enable
    localparam CFG_MOUSE_DIS = 5;   // Mouse disabled

    // Internal registers
    reg [7:0] config_byte;
    reg [7:0] status_reg;
    reg [7:0] output_buffer;
    reg       output_from_mouse;

    // Command state
    reg       expecting_data;
    reg [7:0] pending_cmd;

    // Mouse data FIFO
    reg [7:0] mouse_fifo [0:15];
    reg [3:0] fifo_wr_ptr;
    reg [3:0] fifo_rd_ptr;
    reg [4:0] fifo_count;

    wire fifo_empty = (fifo_count == 0);
    wire fifo_full = (fifo_count == 16);

    // Mouse enabled
    wire mouse_enabled = ~config_byte[CFG_MOUSE_DIS];

    // Output buffer handling
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            config_byte <= 8'h03;  // Default: mouse enabled (bit5=0), interrupts enabled (bit0=KB, bit1=mouse)
            status_reg <= 8'h00;
            output_buffer <= 8'h00;
            output_from_mouse <= 1'b0;
            expecting_data <= 1'b0;
            pending_cmd <= 8'h00;
            fifo_wr_ptr <= 4'h0;
            fifo_rd_ptr <= 4'h0;
            fifo_count <= 5'h0;
            mouse_cmd_valid <= 1'b0;
            mouse_cmd_out <= 8'h00;
        end else begin
            // Clear one-cycle signals
            mouse_cmd_valid <= 1'b0;

            // Handle mouse data input
            if (mouse_data_valid && !fifo_full && mouse_enabled) begin
                mouse_fifo[fifo_wr_ptr] <= mouse_data_in;
                fifo_wr_ptr <= fifo_wr_ptr + 1;
                fifo_count <= fifo_count + 1;
            end

            // Transfer from FIFO to output buffer if empty
            if (!status_reg[STATUS_OBF] && !fifo_empty) begin
                output_buffer <= mouse_fifo[fifo_rd_ptr];
                fifo_rd_ptr <= fifo_rd_ptr + 1;
                fifo_count <= fifo_count - 1;
                status_reg[STATUS_OBF] <= 1'b1;
                status_reg[STATUS_MOBF] <= 1'b1;
                output_from_mouse <= 1'b1;
            end

            // CPU read from data port
            if (io_read && io_address == 8'h00) begin
                status_reg[STATUS_OBF] <= 1'b0;
                status_reg[STATUS_MOBF] <= 1'b0;
                output_from_mouse <= 1'b0;
            end

            // CPU write to data port (0x60)
            if (io_write && io_address == 8'h00) begin
                if (expecting_data) begin
                    expecting_data <= 1'b0;

                    case (pending_cmd)
                        CMD_WRITE_CONFIG: begin
                            config_byte <= io_writedata;
                        end

                        CMD_WRITE_MOUSE: begin
                            // Send byte to mouse
                            mouse_cmd_out <= io_writedata;
                            mouse_cmd_valid <= 1'b1;
                        end

                        default: begin
                            // Unknown command parameter
                        end
                    endcase
                end
            end

            // CPU write to command port (0x64)
            if (io_write && io_address == 8'h04) begin
                case (io_writedata)
                    CMD_READ_CONFIG: begin
                        // Read config byte to output buffer
                        output_buffer <= config_byte;
                        status_reg[STATUS_OBF] <= 1'b1;
                        status_reg[STATUS_MOBF] <= 1'b0;
                        output_from_mouse <= 1'b0;
                    end

                    CMD_WRITE_CONFIG: begin
                        expecting_data <= 1'b1;
                        pending_cmd <= CMD_WRITE_CONFIG;
                    end

                    CMD_DISABLE_MOUSE: begin
                        config_byte[CFG_MOUSE_DIS] <= 1'b1;
                    end

                    CMD_ENABLE_MOUSE: begin
                        config_byte[CFG_MOUSE_DIS] <= 1'b0;
                    end

                    CMD_TEST_MOUSE: begin
                        // Mouse test - return 0x00 for OK
                        output_buffer <= 8'h00;
                        status_reg[STATUS_OBF] <= 1'b1;
                        status_reg[STATUS_MOBF] <= 1'b0;
                        output_from_mouse <= 1'b0;
                    end

                    CMD_SELF_TEST: begin
                        // Self test - return 0x55 for OK
                        output_buffer <= 8'h55;
                        status_reg[STATUS_OBF] <= 1'b1;
                        status_reg[STATUS_MOBF] <= 1'b0;
                        output_from_mouse <= 1'b0;
                    end

                    CMD_WRITE_MOUSE: begin
                        expecting_data <= 1'b1;
                        pending_cmd <= CMD_WRITE_MOUSE;
                    end

                    default: begin
                        // Unknown command
                    end
                endcase
            end
        end
    end

    // Read data mux
    always_comb begin
        case (io_address)
            8'h00: io_readdata = output_buffer;
            8'h04: io_readdata = status_reg;
            default: io_readdata = 8'h00;
        endcase
    end

    // Mouse interrupt (IRQ12)
    // Trigger when mouse data in output buffer and interrupts enabled
    assign irq_mouse = status_reg[STATUS_OBF] &&
                       output_from_mouse &&
                       config_byte[CFG_MOUSE_INT];

endmodule
