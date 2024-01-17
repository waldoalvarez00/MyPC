// Copyright Jamie Iles, 2017
// Copyright Waldo Alvarez, 2023 
// https://pipflow.com
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
module VGAController(input logic clk,
                     input logic sys_clk,
		               input logic reset,
                     output logic fb_access,
                     output logic [15:0] fb_address,
                     input logic fb_ack,
                     input logic [15:0] fb_data,
					 

                     // VGA signals
		             output logic vga_hsync,
		             output logic vga_vsync,
		             output logic [3:0] vga_r,
		             output logic [3:0] vga_g,
		             output logic [3:0] vga_b,
						 
						 
						 output logic H_BLANK,
						 output logic V_BLANK,
						 
						 
						 output logic ce_pix, // Added ce_pix output
					 
                     input logic graphics_enabled,
                     input logic cursor_enabled,
                     input logic bright_colors,
                     input logic palette_sel,
                     input logic [3:0] background_color,
                     input logic [14:0] cursor_pos,
                     input logic [2:0] cursor_scan_start,
                     input logic [2:0] cursor_scan_end,
                     input logic vga_256_color,
                     output logic [7:0] vga_dac_idx,
                     input logic [17:0] vga_dac_rd,
							
							output logic DE
							
							);

wire hsync;
wire vsync;
wire is_blank;
wire [9:0] row;
wire [9:0] col;
logic fdata;

// Putting a 640x400 display into a 640x480 screen.  Black bars of 40 pixels
// at the top and bottom.
wire [9:0] shifted_row = is_border ? 10'b0 : row - 10'd40;
wire is_border = row < 10'd40 || row >= 10'd440;

wire [3:0] fb_background;
wire [3:0] fb_foreground;
wire [7:0] fb_glyph;
logic [2:0] fb_fcl_col;
logic [2:0] fb_fcl_row;
wire render_cursor;
wire [7:0] graphics_colour;

logic [2:0] vsync_pipe;
assign vga_vsync = vsync_pipe[0];
logic [2:0] hsync_pipe;
assign vga_hsync = hsync_pipe[0];

assign vga_dac_idx = graphics_colour;

// Logic to generate the DE signal
always_ff @(posedge clk) begin
    DE <= !is_blank && !H_BLANK && !V_BLANK;
end


VGASync VGASync(
    .clk(clk),             
    .reset(reset),         
    .vsync(vsync),         
    .hsync(hsync),         
    .is_blank(is_blank),   
    .row(row),             
    .col(col),             
    .V_BLANK(V_BLANK),     
    .H_BLANK(H_BLANK)      
);



			
			
FrameBuffer FrameBuffer(
    .glyph(fb_glyph),               
    .background(fb_background),     
    .foreground(fb_foreground),     
    .row(shifted_row),              

    
    .clk(clk),                      
    .sys_clk(sys_clk),              
    .reset(reset),                  
    .is_border(is_border),          
    .fb_access(fb_access),          
    .fb_address(fb_address),        
    .fb_ack(fb_ack),                
    .fb_data(fb_data),              
    .col(col),                      
    .is_blank(is_blank),            
    .cursor_enabled(cursor_enabled),
    .cursor_pos(cursor_pos),        
    .cursor_scan_start(cursor_scan_start), 
    .cursor_scan_end(cursor_scan_end),     
    .graphics_enabled(graphics_enabled),   
    .render_cursor(render_cursor),         
    .vga_256_color(vga_256_color),         
    .graphics_colour(graphics_colour)      
);



FontColorLUT FontColorLUT(
    .glyph(fb_glyph),                   
    .glyph_row(fb_fcl_row),             
    .glyph_col(fb_fcl_col),             
    .foreground(fb_foreground),         
    .background(fb_background),         
    .r(vga_r),                          
    .g(vga_g),                          
    .b(vga_b),                          

    
    .clk(clk),                          
    .render_cursor(render_cursor),      
    .graphics_enabled(graphics_enabled),
    .graphics_colour(graphics_colour),  
    .vga_256_color(vga_256_color),      
    .vga_dac_rd(vga_dac_rd),            
    .bright_colors(bright_colors),      
    .palette_sel(palette_sel),          
    .background_color(background_color) 
);


/*
FontColorLUT FontColorLUT(.glyph(fb_glyph),
                          .glyph_row(fb_fcl_row),
                          .glyph_col(fb_fcl_col),
                          .foreground(fb_foreground),
                          .background(fb_background),
                          .r(vga_r),
                          .g(vga_g),
                          .b(vga_b),
			  .*);*/

always_ff @(posedge clk) begin
    fb_fcl_col <= col[2:0];
    fb_fcl_row <= shifted_row[3:1];
end

always_ff @(posedge clk) begin
    vsync_pipe <= {vsync, vsync_pipe[2:1]};
    hsync_pipe <= {hsync, hsync_pipe[2:1]};
end


// Pixel Clock Divider Logic
localparam integer PIXEL_CLOCK_DIVIDER = 30000000 / 25175000; // Adjust this based on your clk frequency
reg [31:0] pixel_clock_counter = 0;

always_ff @(posedge clk) begin
    if (pixel_clock_counter >= PIXEL_CLOCK_DIVIDER / 2 - 1) begin
        ce_pix <= 1'b1;
        pixel_clock_counter <= pixel_clock_counter + 1'b1;
    end else if (pixel_clock_counter >= PIXEL_CLOCK_DIVIDER - 1) begin
        ce_pix <= 1'b0;
        pixel_clock_counter <= 0;
    end else begin
        pixel_clock_counter <= pixel_clock_counter + 1'b1;
    end
end

endmodule
