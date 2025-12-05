//
// Majority voting filter
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude Code (SystemVerilog)
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//

module slib_mv_filter #(
    parameter WIDTH     = 4,
    parameter THRESHOLD = 10
) (
    input  logic CLK,       // Clock
    input  logic RST,       // Reset
    input  logic SAMPLE,    // Clock enable for sample process
    input  logic CLEAR,     // Reset process
    input  logic D,         // Signal input
    output logic Q          // Signal D was at least THRESHOLD samples high
);

    // Signals
    logic [WIDTH:0] iCounter;   // Sample counter
    logic           iQ;         // Internal Q

    // Main process
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iCounter <= '0;
            iQ       <= 1'b0;
        end else begin
            if (iCounter >= THRESHOLD) begin    // Compare with threshold
                iQ <= 1'b1;
            end else begin
                if (SAMPLE && D) begin          // Take sample
                    iCounter <= iCounter + 1'b1;
                end
            end

            if (CLEAR) begin                    // Reset logic
                iCounter <= '0;
                iQ       <= 1'b0;
            end
        end
    end

    // Output signals
    assign Q = iQ;

endmodule
