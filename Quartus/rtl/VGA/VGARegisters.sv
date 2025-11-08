// Copyright Jamie Iles, 2017, 2018
//
// This file is part of s80x86.
//
// s80x86 is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// s80x86 is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with s80x86.  If not, see <http://www.gnu.org/licenses/>.

`default_nettype none

`include "VGATypes.sv"
module VGARegisters(input wire  clk,
                    input wire  vga_clk,
                    input wire  reset,
						  
                    // Bus
                    input wire  cs,
                    input logic [19:1] data_m_addr,
                    input logic [15:0] data_m_data_in,
                    output logic [15:0] data_m_data_out,
                    input logic [1:0] data_m_bytesel,
                    input logic data_m_wr_en,
                    input logic data_m_access,
                    output logic data_m_ack,
						  
                    // VGA
                    input logic vga_vsync,
                    input logic vga_hsync,
						  
                    // VGA clock domain signals
                    output logic cursor_enabled,
                    output logic graphics_enabled,
                    output logic [3:0] background_color,
                    output logic bright_colors,
                    output logic palette_sel,
                    output logic [14:0] cursor_pos,
                    output logic [2:0] cursor_scan_start,
                    output logic [2:0] cursor_scan_end,
                    output logic vga_256_color,
                    input  logic [7:0] vga_dac_idx,
                    output logic [17:0] vga_dac_rd,

                    // NEW: Video mode number output
                    output VideoModeNumber_t mode_num);

wire reg_access     = cs & data_m_access;

// MCGA Register Address Decode
// MCGA controller uses non-standard addresses to coexist with CGA controller
// Addresses are at 0x1E0-0x1ED (I/O ports 0x3C0-0x3DA equivalent)
// Note: data_m_addr is [19:1], so data_m_addr[4:1] extracts numerical bits [3:0]

wire sel_amcr        = reg_access & (data_m_addr[4:1] == 4'b0000) & data_m_bytesel[0];  // 0x1E0
wire sel_dac_rd_idx  = reg_access & (data_m_addr[4:1] == 4'b0011) & data_m_bytesel[1];  // 0x1E3
wire sel_dac_wr_idx  = reg_access & (data_m_addr[4:1] == 4'b0100) & data_m_bytesel[0];  // 0x1E4
wire sel_dac         = reg_access & (data_m_addr[4:1] == 4'b0100) & data_m_bytesel[1];  // 0x1E4 (DAC data)
wire sel_index       = reg_access & (data_m_addr[4:1] == 4'b1010) & data_m_bytesel[0];  // 0x1EA (CRT Index)
wire sel_value       = reg_access & (data_m_addr[4:1] == 4'b1010) & data_m_bytesel[1];  // 0x1EA (CRT Data)
wire sel_mode        = reg_access & (data_m_addr[4:1] == 4'b1100) & data_m_bytesel[0];  // 0x1EC (Mode Control)
wire sel_color       = reg_access & (data_m_addr[4:1] == 4'b1100) & data_m_bytesel[1];  // 0x1EC (Color Select)
wire sel_status      = reg_access & (data_m_addr[4:1] == 4'b1101) & data_m_bytesel[0];  // 0x1ED (Status)




reg  [5:0] active_index;  // Expanded to 6 bits for VGA CRTC (up to 0x18)
wire [5:0] index = data_m_wr_en & sel_index ? data_m_data_in[5:0] : active_index;
logic [7:0] index_value;

reg [1:0] cursor_mode;
reg display_enabled;
reg hres_mode;           // Bit 0: 1=80 columns, 0=40 columns
reg graphics_320;        // Bit 1: 1=320-wide graphics
reg bw_mode;             // Bit 2: 1=B&W, 0=color
reg mode_640;            // Bit 4: 1=640-wide graphics
reg blink_enabled;       // Bit 5: blinking enabled
reg sys_graphics_enabled;
reg sys_bright_colors;
reg sys_cursor_enabled;
reg sys_palette_sel;
reg [7:0] sys_amcr;
wire sys_256_color = sys_amcr == 8'h41;

// Compatibility aliases
wire text_enabled = hres_mode;  // For backward compatibility

reg [14:0] sys_cursor_pos;
wire load_vga_cursor;
wire rdy_vga_cursor;
wire [14:0] vga_cursor;

logic [2:0] sys_cursor_scan_start;
wire load_cursor_scan_start;
wire [2:0] vga_cursor_scan_start;

logic [2:0] sys_cursor_scan_end;
wire load_cursor_scan_end;
wire [2:0] vga_cursor_scan_end;

logic [3:0] sys_background_color;
wire load_background_color;
wire [3:0] vga_background_color;

// CRTC registers for resolution detection
reg [7:0] crtc_horiz_display_end;    // Register 0x01: Horizontal Display End
reg [7:0] crtc_vert_display_end_low; // Register 0x12: Vertical Display End (low byte)
reg [7:0] crtc_overflow;             // Register 0x07: Overflow register
reg [4:0] crtc_max_scan_line;        // Register 0x09: Maximum Scan Line

reg [17:0] sys_dac_rd;
reg [7:0] dac_wr_idx;
reg [7:0] dac_rd_idx;
reg [11:0] dac_component_rg;
reg [1:0] dac_wr_offs;
reg [1:0] dac_rd_offs;

reg vga_send;

// Reset initialization moved to always_ff blocks to avoid driver conflicts in Icarus Verilog

// Mode detection logic
// Detect current video mode based on register settings
logic [7:0] sys_mode_num;

// Extract vertical display end from CRTC registers (10-bit value)
// Bit 8 is in overflow[1], bit 9 is in overflow[6]
wire [9:0] vert_display_end = {crtc_overflow[6], crtc_overflow[1], crtc_vert_display_end_low};

// Helper: Detect resolution ranges
wire is_200_lines  = (vert_display_end >= 10'd190) && (vert_display_end <= 10'd210);  // ~200 lines
wire is_350_lines  = (vert_display_end >= 10'd340) && (vert_display_end <= 10'd360);  // ~350 lines
wire is_400_lines  = (vert_display_end >= 10'd390) && (vert_display_end <= 10'd410);  // ~400 lines
wire is_480_lines  = (vert_display_end >= 10'd470) && (vert_display_end <= 10'd490);  // ~480 lines

// Helper: Detect column modes (register holds columns-1)
wire is_40_col = (crtc_horiz_display_end >= 8'd38) && (crtc_horiz_display_end <= 8'd41);  // ~40 columns
wire is_80_col = (crtc_horiz_display_end >= 8'd78) && (crtc_horiz_display_end <= 8'd81);  // ~80 columns

// Helper: Detect MDA mode (720x350 monochrome text)
wire is_mda_mode = is_350_lines && (crtc_horiz_display_end >= 8'd88) && (crtc_horiz_display_end <= 8'd92);  // ~90 columns

always_comb begin
    // Default to mode 03h (80x25 text color)
    sys_mode_num = MODE_03H;

    // Priority-based mode detection
    if (sys_256_color) begin
        // Mode 13h: 320x200, 256 colors (MCGA/VGA)
        sys_mode_num = MODE_13H;

    end else if (is_mda_mode) begin
        // Mode 07h: 80x25 text, monochrome (MDA/Hercules)
        sys_mode_num = MODE_07H;

    end else if (is_480_lines) begin
        // VGA 640x480 modes
        if (mode_640 || graphics_320) begin
            // Graphics mode
            if (bw_mode) begin
                // Mode 11h: 640x480, 2 colors
                sys_mode_num = MODE_11H;
            end else begin
                // Mode 12h: 640x480, 16 colors
                sys_mode_num = MODE_12H;
            end
        end
        // Could be text mode at 640x480, default to 03h

    end else if (is_350_lines) begin
        // EGA 640x350 modes
        if (mode_640 || graphics_320) begin
            // Graphics mode
            if (bw_mode) begin
                // Mode 0Fh: 640x350, monochrome
                sys_mode_num = MODE_0FH;
            end else begin
                // Mode 10h: 640x350, 16 colors
                sys_mode_num = MODE_10H;
            end
        end
        // Could be EGA text mode, default to 03h

    end else if (is_200_lines || is_400_lines) begin
        // CGA/MCGA 200-line modes (or 400-line doubled)
        if (mode_640) begin
            // CGA/EGA hi-res graphics (640x200)
            // Distinguish between CGA (2-color) and EGA (16-color) using bw_mode
            // CGA mode 06h typically has bw_mode=1, EGA 0Eh has bw_mode=0
            if (bw_mode) begin
                // CGA 640x200, 2 colors (mode 06h)
                sys_mode_num = MODE_06H;
            end else begin
                // EGA 640x200, 16 colors (mode 0Eh)
                sys_mode_num = MODE_0EH;
            end

        end else if (graphics_320) begin
            // 320x200 graphics modes
            if (is_40_col || (crtc_horiz_display_end <= 8'd41)) begin
                // CGA 320x200 modes
                if (bw_mode) begin
                    sys_mode_num = MODE_05H;  // 320x200, 4 grays
                end else begin
                    sys_mode_num = MODE_04H;  // 320x200, 4 colors
                end
            end else begin
                // EGA 320x200, 16 colors
                sys_mode_num = MODE_0DH;
            end

        end else begin
            // Text modes
            if (is_40_col || !hres_mode) begin
                // 40-column text
                if (bw_mode) begin
                    sys_mode_num = MODE_00H;  // 40x25 text, B&W
                end else begin
                    sys_mode_num = MODE_01H;  // 40x25 text, 16 colors
                end
            end else begin
                // 80-column text
                if (bw_mode) begin
                    sys_mode_num = MODE_02H;  // 80x25 text, B&W
                end else begin
                    sys_mode_num = MODE_03H;  // 80x25 text, 16 colors
                end
            end
        end
    end
end

// Synchronize mode number to VGA clock domain
BusSync #(.WIDTH(8))
        ModeNumSync(.clk(vga_clk),
                    .reset(reset),
                    .d(sys_mode_num),
                    .q(mode_num));

always_ff @(posedge clk)
    vga_send <= rdy_vga_cursor && vsync;

wire hsync;
wire vsync;

BitSync         HsyncSync(.clk(clk),
                          .reset(reset),
                          .d(vga_hsync),
                          .q(hsync));
								  
								  
BitSync         VsyncSync(.clk(clk),
                          .reset(reset),
                          .d(vga_vsync),
                          .q(vsync));
								  
								  
BitSync         GraphicsEnabledSync(.clk(vga_clk),
                                    .reset(reset),
                                    .d(sys_graphics_enabled),
                                    .q(graphics_enabled));
												
												
												
BitSync         BrightColorsSync(.clk(vga_clk),
                                 .reset(reset),
                                 .d(sys_bright_colors),
                                 .q(bright_colors));
											
											
											
BitSync         CursorEnabledSync(.clk(vga_clk),
                                  .reset(reset),
                                  .d(sys_cursor_enabled),
                                  .q(cursor_enabled));
											 
											 
											 
BitSync         PaletteSelSync(.clk(vga_clk),
                               .reset(reset),
                               .d(sys_palette_sel),
                               .q(palette_sel));
										 
										 
										 
BitSync         Is256ColorSelSync(.clk(vga_clk),
                                  .reset(reset),
                                  .d(sys_256_color),
                                  .q(vga_256_color));
											 
											 
											 
MCP             #(.width(15),
                  .reset_val(15'b0))
                CursorMCP(.reset(reset),
                          .clk_a(clk),
                          .a_ready(rdy_vga_cursor),
                          .a_datain(sys_cursor_pos),
                          .a_send(vga_send),
                          .clk_b(vga_clk),
                          .b_data(vga_cursor),
                          .b_load(load_vga_cursor));
								  
								  
								  

MCP             #(.width(3),
                  .reset_val(3'b0))
                CursorScanStartMCP(.reset(reset),
                                   .clk_a(clk),
                                   .a_ready(),
                                   .a_datain(sys_cursor_scan_start),
                                   .a_send(vga_send),
                                   .clk_b(vga_clk),
                                   .b_data(vga_cursor_scan_start),
                                   .b_load(load_cursor_scan_start));
											  
											  
											  
MCP             #(.width(3),
                  .reset_val(3'b0))
                CursorScanEndMCP(.reset(reset),
                                 .clk_a(clk),
                                 .a_ready(),
                                 .a_datain(sys_cursor_scan_end),
                                 .a_send(vga_send),
                                 .clk_b(vga_clk),
                                 .b_data(vga_cursor_scan_end),
                                 .b_load(load_cursor_scan_end));
											
											
											
MCP             #(.width(4),
                  .reset_val(4'b0))
                BackgroundColorMCP(.reset(reset),
                                   .clk_a(clk),
                                   .a_ready(),
                                   .a_datain(sys_background_color),
                                   .a_send(vga_send),
                                   .clk_b(vga_clk),
                                   .b_data(vga_background_color),
                                   .b_load(load_background_color));
											  
											  

always_ff @(posedge vga_clk) begin

    if (load_vga_cursor)
        cursor_pos <= vga_cursor;
		  
    if (load_cursor_scan_start)
        cursor_scan_start <= vga_cursor_scan_start;
		  
    if (load_cursor_scan_end)
        cursor_scan_end <= vga_cursor_scan_end;

    if (load_background_color)
        background_color <= vga_background_color;
		  
end





// Status register 3DAh

wire [7:0] status = {4'b0, vga_vsync, 2'b0, (~vsync | ~hsync)};




always_ff @(posedge clk)
    sys_cursor_enabled <= cursor_mode != 2'b01;
	 
	 

DACRam DACRam(.clock_a(clk),
              .address_a(data_m_wr_en ? dac_wr_idx : dac_rd_idx),
              .data_a({dac_component_rg, data_m_data_in[13:8]}),
              .wren_a(sel_dac && data_m_wr_en && dac_wr_offs == 2'b10),
              .q_a(sys_dac_rd),
              .clock_b(vga_clk),
              .address_b(vga_dac_idx),
              .data_b(18'b0),
              .wren_b(1'b0),
              .q_b(vga_dac_rd));
				  
				  
				  

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        dac_wr_idx <= 8'h00;
        dac_rd_idx <= 8'h00;
        dac_wr_offs <= 2'b00;
        dac_rd_offs <= 2'b00;
        dac_component_rg <= 12'h000;
    end else begin
        if (sel_dac_wr_idx & dac_ack_edge) begin
            dac_wr_idx <= data_m_data_in[7:0];
            dac_wr_offs <= 2'b00;
        end

        if (sel_dac_rd_idx & dac_ack_edge) begin
            dac_rd_idx <= data_m_data_in[15:8];
            dac_rd_offs <= 2'b00;
        end

        // Only increment on rising edge of ACK to prevent multiple increments
        if (sel_dac & data_m_wr_en & dac_ack_edge) begin
            if (dac_wr_offs == 2'b10) begin
                dac_wr_idx <= dac_wr_idx + 1'b1;
                dac_wr_offs <= 2'b00;
            end else begin
                dac_component_rg <= {dac_component_rg[5:0], data_m_data_in[13:8]};
                dac_wr_offs <= dac_wr_offs + 1'b1;
            end
        end

        if (sel_dac & ~data_m_wr_en & dac_ack_edge) begin
            if (dac_rd_offs == 2'b10) begin
                dac_rd_idx <= dac_rd_idx + 1'b1;
                dac_rd_offs <= 2'b00;
            end else begin
                dac_rd_offs <= dac_rd_offs + 1'b1;
            end
        end
    end
end






always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        crtc_horiz_display_end <= 8'd79;     // Default: 80 columns - 1
        crtc_vert_display_end_low <= 8'd191; // Default: 200 lines - 1 (low byte)
        crtc_overflow <= 8'h00;
        crtc_max_scan_line <= 5'd7;          // Default: 8-line characters
        cursor_mode <= 2'b00;
        sys_cursor_scan_start <= 3'b000;
        sys_cursor_scan_end <= 3'b000;
        sys_cursor_pos <= 15'h0000;
    end else if (data_m_wr_en & sel_value) begin
        case (index)
        6'h01: crtc_horiz_display_end <= data_m_data_in[15:8];      // Horizontal Display End
        6'h07: crtc_overflow <= data_m_data_in[15:8];               // Overflow register
        6'h09: crtc_max_scan_line <= data_m_data_in[12:8];          // Maximum Scan Line
        6'h0a: {cursor_mode, sys_cursor_scan_start} <=
            {data_m_data_in[13:12], data_m_data_in[10:8]};
        6'h0b: sys_cursor_scan_end <= data_m_data_in[10:8];
        6'h0e: sys_cursor_pos[14:8] <= data_m_data_in[14:8];
        6'h0f: sys_cursor_pos[7:0] <= data_m_data_in[15:8];
        6'h12: crtc_vert_display_end_low <= data_m_data_in[15:8];   // Vertical Display End (low)
        default: ;
        endcase
    end
end





always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        sys_palette_sel <= 1'b0;
        sys_bright_colors <= 1'b0;
        sys_background_color <= 4'h0;
    end else if (data_m_wr_en & sel_color) begin
        {sys_palette_sel, sys_bright_colors, sys_background_color} <=
            data_m_data_in[13:8];
    end
end




always_ff @(posedge clk or posedge reset)
    if (reset) begin
        hres_mode <= 1'b1;           // Default: 80 columns
        graphics_320 <= 1'b0;
        bw_mode <= 1'b0;             // Default: color
        display_enabled <= 1'b1;
        mode_640 <= 1'b0;
        blink_enabled <= 1'b0;
        sys_graphics_enabled <= 1'b0;  // Fix: Initialize to 0 (text mode)
    end else if (sel_mode && data_m_wr_en) begin
        hres_mode <= data_m_data_in[0];
        graphics_320 <= data_m_data_in[1];
        bw_mode <= data_m_data_in[2];
        display_enabled <= data_m_data_in[3];
        mode_640 <= data_m_data_in[4];
        blink_enabled <= data_m_data_in[5];
        // Set sys_graphics_enabled for compatibility
        sys_graphics_enabled <= data_m_data_in[1] | data_m_data_in[4];
    end

// 3D8 Mode Port
// 0 - 80/40 alpha mode
// 1 - 1 320-wide, 0 all others
// 2 - foreground color
// 3 - video enabled
// 4 - 640-wide graphics
// 5 - blinking
// 6 - zero unused
// 7 - zero unused

				
				
				
always_ff @(posedge clk or posedge reset)
    if (reset)
        active_index <= 6'h0;
    else if (sel_index & data_m_wr_en)
        active_index <= data_m_data_in[5:0];  // 6 bits for VGA CRTC

		  
		  
always_ff @(posedge clk or posedge reset)
    if (reset)
        sys_amcr <= 8'h00;
    else if (sel_amcr & data_m_wr_en)
        sys_amcr <= data_m_data_in[7:0];

		  
		  
		  
		  

always_comb begin

    case (index)
    6'h01: index_value = crtc_horiz_display_end;
    6'h07: index_value = crtc_overflow;
    6'h09: index_value = {3'b0, crtc_max_scan_line};
    6'h0a: index_value = {2'b0, cursor_mode, 1'b0, sys_cursor_scan_start};
    6'h0b: index_value = {5'b0, sys_cursor_scan_end};
    6'h0e: index_value = {1'b0, sys_cursor_pos[14:8]};  // 7 bits [14:8], bit 7 unused
    6'h0f: index_value = sys_cursor_pos[7:0];
    6'h12: index_value = crtc_vert_display_end_low;
    default: index_value = 8'b0;
    endcase

end






// Fix: Use always_comb to build output, then register it for Icarus Verilog compatibility
logic [15:0] data_out_comb;

always_comb begin
    data_out_comb = 16'b0;

    if (!data_m_wr_en) begin
        if (sel_index)
            data_out_comb[7:0] = {2'b0, active_index};

        if (sel_mode)
            data_out_comb[7:0] = {2'b0, blink_enabled, mode_640,
                                  display_enabled, bw_mode,
                                  graphics_320, hres_mode};
        if (sel_status)
            data_out_comb[7:0] = status;

        if (sel_value)
            data_out_comb[15:8] = index_value;

        if (sel_color)
            data_out_comb[15:8] = {2'b0, sys_palette_sel, sys_bright_colors,
                                   sys_background_color};
        if (sel_amcr)
            data_out_comb[7:0] = sys_amcr;

        if (sel_dac) begin
            if (dac_rd_offs == 2'b10)
                data_out_comb[15:8] = {2'b0, sys_dac_rd[5:0]};
            else if (dac_rd_offs == 2'b01)
                data_out_comb[15:8] = {2'b0, sys_dac_rd[11:6]};
            else if (dac_rd_offs == 2'b00)
                data_out_comb[15:8] = {2'b0, sys_dac_rd[17:12]};
        end
    end
end

always_ff @(posedge clk) begin
    data_m_data_out <= data_out_comb;
end

// Track ACK state to detect rising edge for DAC offset increment
reg data_m_ack_prev;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        data_m_ack_prev <= 1'b0;
    end else begin
        data_m_ack_prev <= data_m_ack;
    end
end

// Only increment DAC offsets on rising edge of ACK
wire dac_ack_edge = data_m_ack && !data_m_ack_prev;

always_ff @(posedge clk)
    data_m_ack <= data_m_access && cs;

endmodule
