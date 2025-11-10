// VGA Adapter - Top-Level Module
// Complete VGA subsystem for PC-compatible video
// Supports all 15 standard video modes (CGA, EGA, VGA, MDA, MCGA)
//
// Features:
// - 15 video modes from 40x25 text to 640x480 graphics
// - Automatic mode detection from CRTC registers
// - Integrated framebuffer with prefetch
// - 256-color DAC palette support
// - Text and graphics rendering
// - Cursor support
//
// Copyright 2024

`timescale 1ns/1ps
`default_nettype none

`include "VGATypes.sv"

module VGA_Adapter (
    // Clock and reset
    input logic sys_clk,           // System clock (50 MHz typical)
    input logic vga_clk,           // VGA pixel clock (25 MHz typical)
    input logic reset,

    // CPU bus interface (for VGA registers)
    input logic cs,                // Chip select
    input logic [19:1] data_m_addr,
    input logic [15:0] data_m_data_in,
    output logic [15:0] data_m_data_out,
    input logic [1:0] data_m_bytesel,
    input logic data_m_wr_en,
    input logic data_m_access,
    output logic data_m_ack,

    // Framebuffer memory interface
    output logic fb_access,        // Framebuffer access request
    output logic [15:0] fb_address,
    input logic fb_ack,
    input logic [15:0] fb_data,

    // VGA output signals
    output logic vga_hsync,
    output logic vga_vsync,
    output logic [3:0] vga_r,
    output logic [3:0] vga_g,
    output logic [3:0] vga_b,
    output logic vga_de,           // Display enable
    output logic vga_h_blank,
    output logic vga_v_blank,
    output logic vga_ce_pix,       // Pixel clock enable

    // Video mode output (for debugging/status)
    output VideoModeNumber_t mode_num
);

    // Internal signals from VGARegisters to VGAController
    logic cursor_enabled;
    logic graphics_enabled;
    logic [3:0] background_color;
    logic bright_colors;
    logic palette_sel;
    logic [14:0] cursor_pos;
    logic [2:0] cursor_scan_start;
    logic [2:0] cursor_scan_end;
    logic vga_256_color;
    logic [7:0] vga_dac_idx;
    logic [17:0] vga_dac_rd;

    // VGA Registers Module
    // Handles CPU register access, mode detection, and DAC palette
    VGARegisters VGARegisters_inst (
        .clk(sys_clk),
        .vga_clk(vga_clk),
        .reset(reset),
        // Bus interface
        .cs(cs),
        .data_m_addr(data_m_addr),
        .data_m_data_in(data_m_data_in),
        .data_m_data_out(data_m_data_out),
        .data_m_bytesel(data_m_bytesel),
        .data_m_wr_en(data_m_wr_en),
        .data_m_access(data_m_access),
        .data_m_ack(data_m_ack),
        // VGA sync feedback
        .vga_vsync(vga_vsync),
        .vga_hsync(vga_hsync),
        // VGA control outputs
        .cursor_enabled(cursor_enabled),
        .graphics_enabled(graphics_enabled),
        .background_color(background_color),
        .bright_colors(bright_colors),
        .palette_sel(palette_sel),
        .cursor_pos(cursor_pos),
        .cursor_scan_start(cursor_scan_start),
        .cursor_scan_end(cursor_scan_end),
        .vga_256_color(vga_256_color),
        .vga_dac_idx(vga_dac_idx),
        .vga_dac_rd(vga_dac_rd),
        .mode_num(mode_num)
    );

    // VGA Controller Module
    // Generates sync, manages framebuffer, and renders pixels
    VGAController VGAController_inst (
        .clk(vga_clk),
        .sys_clk(sys_clk),
        .reset(reset),
        // Framebuffer interface
        .fb_access(fb_access),
        .fb_address(fb_address),
        .fb_ack(fb_ack),
        .fb_data(fb_data),
        // VGA outputs
        .vga_hsync(vga_hsync),
        .vga_vsync(vga_vsync),
        .vga_r(vga_r),
        .vga_g(vga_g),
        .vga_b(vga_b),
        .H_BLANK(vga_h_blank),
        .V_BLANK(vga_v_blank),
        .ce_pix(vga_ce_pix),
        .DE(vga_de),
        // Control inputs from registers
        .graphics_enabled(graphics_enabled),
        .cursor_enabled(cursor_enabled),
        .bright_colors(bright_colors),
        .palette_sel(palette_sel),
        .background_color(background_color),
        .cursor_pos(cursor_pos),
        .cursor_scan_start(cursor_scan_start),
        .cursor_scan_end(cursor_scan_end),
        .vga_256_color(vga_256_color),
        .vga_dac_idx(vga_dac_idx),
        .vga_dac_rd(vga_dac_rd),
        .mode_num(mode_num)
    );

endmodule

`default_nettype wire
