//
// Counter
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude Code (SystemVerilog)
// Date:     27.01.2008 (original)
// Version:  1.2
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

module slib_counter #(
    parameter WIDTH = 4     // Counter width
) (
    input  logic                 CLK,        // Clock
    input  logic                 RST,        // Reset
    input  logic                 CLEAR,      // Clear counter register
    input  logic                 LOAD,       // Load counter register
    input  logic                 ENABLE,     // Enable count operation
    input  logic                 DOWN,       // Count direction down
    input  logic [WIDTH-1:0]     D,          // Load counter register input
    output logic [WIDTH-1:0]     Q,          // Counter output
    output logic                 OVERFLOW    // Counter overflow
);

    // Counter register (extra bit for overflow detection)
    logic [WIDTH:0] iCounter;

    // Counter process
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iCounter <= '0;                         // Reset counter register
        end else begin
            if (CLEAR) begin
                iCounter <= '0;                     // Clear counter register
            end else if (LOAD) begin                // Load counter register
                iCounter <= {1'b0, D};
            end else if (ENABLE) begin              // Enable counter
                if (!DOWN) begin                    // Count up
                    iCounter <= iCounter + 1'b1;
                end else begin                      // Count down
                    iCounter <= iCounter - 1'b1;
                end
            end

            if (iCounter[WIDTH]) begin              // Clear overflow bit
                iCounter[WIDTH] <= 1'b0;
            end
        end
    end

    // Output ports
    assign Q        = iCounter[WIDTH-1:0];
    assign OVERFLOW = iCounter[WIDTH];

endmodule
