// Stub for MiSTer hps_io module
// This is a simplified stub for Verilator linting purposes only

module hps_io #(
    parameter CONF_STR = "",
    parameter PS2DIV = 10,
    parameter PS2WE = 1,
    parameter WIDE = 1
) (
    input         clk_sys,
    inout  [48:0] HPS_BUS,
    output [31:0] gamma_bus,

    output        forced_scandoubler,
    output  [1:0] buttons,
    output [127:0] status,
    input  [127:0] status_menumask,

    output [10:0] ps2_key,

    output        ps2_kbd_clk_out,
    output        ps2_kbd_data_out,
    input         ps2_kbd_clk_in,
    input         ps2_kbd_data_in,

    input  [15:0] sdram_sz,

    output        ps2_mouse_clk_out,
    output        ps2_mouse_data_out,
    input         ps2_mouse_clk_in,
    input         ps2_mouse_data_in
);

    // Stub implementation - just provide defaults
    assign forced_scandoubler = 1'b0;
    assign buttons = 2'b00;
    assign status = 128'h0;
    assign ps2_key = 11'h0;
    assign ps2_kbd_clk_out = 1'b1;
    assign ps2_kbd_data_out = 1'b1;
    assign ps2_mouse_clk_out = 1'b1;
    assign ps2_mouse_data_out = 1'b1;
    assign gamma_bus = 32'h0;

endmodule
