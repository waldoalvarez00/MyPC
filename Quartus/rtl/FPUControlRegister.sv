// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// FPU Control Word Register
// I/O Ports: 0xF8-0xFB (Write)
//
// Allows CPU to write FPU control word via I/O port

module FPUControlRegister(
    input wire clk,
    input wire reset,
    input wire cs,                      // Chip select (from address decoder)
    input wire [15:0] data_m_data_in,   // Data from CPU
    input wire data_m_wr_en,            // Write enable
    output reg data_m_ack,              // Acknowledge
    output wire [15:0] control_word_out, // Control word to FPU
    output reg control_write            // Pulse when control word written
);

    reg [15:0] control_word;

    // Default 8087 control word: 0x037F
    // Bit 0-5: Exception masks (all masked)
    // Bit 8-9: Precision control (64-bit)
    // Bit 10-11: Rounding control (round to nearest)
    initial begin
        control_word = 16'h037F;
        control_write = 1'b0;
    end

    assign control_word_out = control_word;

    always @(posedge clk) begin
        if (reset) begin
            control_word <= 16'h037F;  // Reset to default
            data_m_ack <= 1'b0;
            control_write <= 1'b0;
        end else begin
            data_m_ack <= cs;  // Acknowledge on chip select
            control_write <= 1'b0;  // Default: no write

            if (cs && data_m_wr_en) begin
                control_word <= data_m_data_in;
                control_write <= 1'b1;  // Pulse for one cycle
            end
        end
    end

endmodule
