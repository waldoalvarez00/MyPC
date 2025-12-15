//
// Majority voting filter
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude Code (SystemVerilog)
// Date:     27.01.2008 (original)
// Version:  1.1
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This code is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the
// Free Software  Foundation, Inc., 59 Temple Place, Suite 330,
// Boston, MA  02111-1307  USA
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
