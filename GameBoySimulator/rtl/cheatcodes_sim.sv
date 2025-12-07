//
// Cheatcodes Simulation Stub
// Disables Game Genie/cheat functionality for simulation
//

module CODES #(
    parameter ACTIVE = 1,
    parameter INDEX_SIZE = 4,
    parameter CODE_WIDTH = 129,
    parameter MAX_CODES = 16,
    parameter DATA_WIDTH = 8,
    parameter COMP_WIDTH = 8,
    parameter ADDR_WIDTH = 16,
    parameter DATA_S = CODE_WIDTH - 1,
    parameter COMP_S = DATA_S - DATA_WIDTH,
    parameter ADDR_S = COMP_S - COMP_WIDTH,
    parameter ENA_F_S = ADDR_S - ADDR_WIDTH,
    parameter COMP_F_S = ENA_F_S - 1,
    parameter ENA_BIT = ENA_F_S
) (
    input                     clk,
    input                     reset,
    input  [CODE_WIDTH-1:0]   code,
    input                     enable,
    input  [ADDR_WIDTH-1:0]   addr_in,
    input  [DATA_WIDTH-1:0]   data_in,
    output                    available,
    output                    genie_ovr,
    output [DATA_WIDTH-1:0]   genie_data
);

    // Cheat codes disabled for simulation
    assign available = 1'b0;
    assign genie_ovr = 1'b0;
    assign genie_data = data_in;

endmodule
