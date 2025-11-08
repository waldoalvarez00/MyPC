//
// Input filter
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude AI (VHDL to SystemVerilog)
// Date:     06.03.2008 (original)
// Version:  1.0
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.

`default_nettype none

module slib_input_filter #(
    parameter SIZE = 4      // Filter counter size
)(
    input  logic CLK,       // Clock
    input  logic RST,       // Reset
    input  logic CE,        // Clock enable
    input  logic D,         // Signal input
    output logic Q          // Signal output
);

    int iCount;

    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iCount <= 0;
            Q <= 1'b0;
        end else begin
            // Input counter
            if (CE) begin
                if (D && iCount != SIZE) begin
                    iCount <= iCount + 1;
                end else if (!D && iCount != 0) begin
                    iCount <= iCount - 1;
                end
            end

            // Output
            if (iCount == SIZE) begin
                Q <= 1'b1;
            end else if (iCount == 0) begin
                Q <= 1'b0;
            end
        end
    end

endmodule

`default_nettype wire
