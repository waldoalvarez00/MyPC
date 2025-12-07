//
// GameBoy State Manager Stub
// (Verilog replacement for gb_statemanager.vhd)
//
// This stub disables state management for Verilator simulation.
//
// Copyright (c) 2024 - MIT License
//

module gb_statemanager #(
    parameter REWIND_SIZE = 58720256,
    parameter REWIND_ADDR = 33554432
) (
    input         clk,
    input         reset,

    input         rewind_on,
    output        rewind_active,

    input  [1:0]  savestate_number,
    input         save,
    input         load,

    output        sleep_rewind,
    input         vsync,

    output        request_savestate,
    output        request_loadstate,
    output [31:0] request_address,
    input         request_busy
);

    // Rewind disabled
    assign rewind_active = 1'b0;
    assign sleep_rewind = 1'b0;

    // Savestate requests disabled
    assign request_savestate = 1'b0;
    assign request_loadstate = 1'b0;
    assign request_address = 32'h0;

endmodule
