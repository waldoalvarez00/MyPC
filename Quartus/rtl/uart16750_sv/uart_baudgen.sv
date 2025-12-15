//
// UART Baudrate generator
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude AI (VHDL to SystemVerilog)
// Date:     27.01.2008 (original)
// Version:  1.1
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.

`default_nettype none

module uart_baudgen (
    input  logic        CLK,        // Clock
    input  logic        RST,        // Reset
    input  logic        CE,         // Clock enable
    input  logic        CLEAR,      // Reset generator (synchronization)
    input  logic [15:0] DIVIDER,    // Clock divider
    output logic        BAUDTICK    // 16xBaudrate tick
);

    logic [15:0] iCounter;

    // Baudrate counter
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iCounter <= 16'h0000;
            BAUDTICK <= 1'b0;
        end else begin
            if (CLEAR) begin
                iCounter <= 16'h0000;
            end else if (CE) begin
                iCounter <= iCounter + 16'd1;
            end

            BAUDTICK <= 1'b0;
            if (iCounter == DIVIDER) begin
                iCounter <= 16'h0000;
                BAUDTICK <= 1'b1;
            end
        end
    end

endmodule

`default_nettype wire
