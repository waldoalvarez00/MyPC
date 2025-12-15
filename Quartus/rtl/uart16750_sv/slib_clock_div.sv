//
// Clock divider (clock enable generator)
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

module slib_clock_div #(
    parameter RATIO = 4     // Clock divider ratio
)(
    input  logic CLK,       // Clock
    input  logic RST,       // Reset
    input  logic CE,        // Clock enable input
    output logic Q          // New clock enable output
);

    logic iQ;
    int iCounter;

    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iCounter <= 0;
            iQ <= 1'b0;
        end else begin
            iQ <= 1'b0;
            if (CE) begin
                if (iCounter == (RATIO - 1)) begin
                    iQ <= 1'b1;
                    iCounter <= 0;
                end else begin
                    iCounter <= iCounter + 1;
                end
            end
        end
    end

    // Output
    assign Q = iQ;

endmodule

`default_nettype wire
