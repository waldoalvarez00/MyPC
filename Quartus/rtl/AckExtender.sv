// Copyright 2025, Waldo Alvarez, https://pipflow.com
`default_nettype none

module AckExtender #(
    parameter integer EXTEND_CYCLES = 3 // Number of cycles to extend the ack signal
)(
    input logic clk,           // Clock input
    input logic rst_n,         // Active high reset
    input logic ack_in,        // Input ack signal
    output logic ack_out       // Extended ack signal
);

    // State variable for counting cycles
    integer counter;

    // Combinational logic to set ack_out immediately
    assign ack_out = ack_in || (counter > 0);

    always_ff @(posedge clk or posedge rst_n) begin
        if (rst_n) begin
            // Reset state
            counter <= 0;
        end else begin
            if (ack_in) begin
                // Start extending ack signal
                counter <= EXTEND_CYCLES;
            end else if (counter > 0) begin
                // Continue extending ack signal
                counter <= counter - 1;
            end
        end
    end
endmodule

