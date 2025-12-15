// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// FPU Status Word Register
// I/O Ports: 0xFC-0xFF (Read)
//
// Allows CPU to read FPU status word via I/O port

module FPUStatusRegister(
    input wire clk,
    input wire reset,
    input wire cs,                      // Chip select (from address decoder)
    input wire [15:0] status_word_in,   // Status word from FPU
    output wire [15:0] data_m_data_out, // Data to CPU
    output reg data_m_ack               // Acknowledge
);

    assign data_m_data_out = status_word_in;

    always @(posedge clk) begin
        if (reset) begin
            data_m_ack <= 1'b0;
        end else begin
            data_m_ack <= cs;  // Acknowledge on chip select
        end
    end

endmodule
