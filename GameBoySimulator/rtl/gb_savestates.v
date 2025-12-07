//
// GameBoy Savestate Module Stub
// (Verilog replacement for gb_savestates.vhd)
//
// This stub disables savestate functionality for Verilator simulation.
// Replace with full implementation for MiSTer FPGA deployment.
//
// Copyright (c) 2024 - MIT License
//

module gb_savestates (
    input         clk,
    input         reset_in,
    output        reset_out,

    output        load_done,

    input         increaseSSHeaderCount,
    input         save,
    input         load,
    input  [31:0] savestate_address,
    output        savestate_busy,

    input  [3:0]  cart_ram_size,

    input         lcd_vsync,

    output [63:0] BUS_Din,
    output [9:0]  BUS_Adr,
    output        BUS_wren,
    output        BUS_rst,
    input  [63:0] BUS_Dout,

    output        sleep_savestate,
    input         clock_ena_in,

    output [19:0] Save_RAMAddr,
    output        Save_RAMWrEn,
    output [7:0]  Save_RAMWriteData,
    input  [7:0]  Save_RAMReadData_WRAM,
    input  [7:0]  Save_RAMReadData_VRAM,
    input  [7:0]  Save_RAMReadData_ORAM,
    input  [7:0]  Save_RAMReadData_ZRAM,
    input  [7:0]  Save_RAMReadData_CRAM,

    input  [63:0] bus_out_Din,
    output [63:0] bus_out_Dout,
    input  [25:0] bus_out_Adr,
    input         bus_out_rnw,
    input         bus_out_ena,
    input  [7:0]  bus_out_be,
    output        bus_out_done
);

    // Pass through reset
    assign reset_out = reset_in;

    // Savestate disabled
    assign load_done = 1'b0;
    assign savestate_busy = 1'b0;
    assign sleep_savestate = 1'b0;

    // Bus outputs disabled
    assign BUS_Din = 64'h0;
    assign BUS_Adr = 10'h0;
    assign BUS_wren = 1'b0;
    assign BUS_rst = reset_in;

    // RAM access disabled
    assign Save_RAMAddr = 20'h0;
    assign Save_RAMWrEn = 1'b0;
    assign Save_RAMWriteData = 8'h0;

    // External bus disabled
    assign bus_out_Dout = 64'h0;
    assign bus_out_done = 1'b1;

endmodule
