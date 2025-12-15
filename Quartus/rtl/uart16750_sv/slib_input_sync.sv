//
// Input synchronization
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude AI (VHDL to SystemVerilog)
// Date:     27.01.2008 (original)
// Version:  1.0
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.

`default_nettype none

module slib_input_sync (
    input  logic CLK,       // Clock
    input  logic RST,       // Reset
    input  logic D,         // Signal input
    output logic Q          // Signal output
);

    logic [1:0] iD;

    // Double-flop synchronizer
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iD <= 2'b00;
        end else begin
            iD[0] <= D;
            iD[1] <= iD[0];
        end
    end

    // Output
    assign Q = iD[1];

endmodule

`default_nettype wire
