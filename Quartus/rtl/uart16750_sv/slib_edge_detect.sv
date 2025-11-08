//
// Signal edge detect
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

module slib_edge_detect (
    input  logic CLK,       // Clock
    input  logic RST,       // Reset
    input  logic D,         // Signal input
    output logic RE,        // Rising edge detected
    output logic FE         // Falling edge detected
);

    logic iDd;              // D register

    // Store D
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iDd <= 1'b0;
        end else begin
            iDd <= D;
        end
    end

    // Output ports
    assign RE = (~iDd & D);
    assign FE = (iDd & ~D);

endmodule

`default_nettype wire
