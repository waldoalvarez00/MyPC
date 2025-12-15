// Copyright Jamie Iles, 2017
// Modified 2024 - Configurable timing for all PC video modes
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

module VGASync(input logic clk,
               input logic reset,
               input VideoModeNumber_t mode_num,  // NEW: Mode input
               output logic vsync,
               output logic hsync,
               output logic is_blank,
               output logic [10:0] row,           // Expanded to 11 bits
               output logic [10:0] col,           // Expanded to 11 bits
               output logic V_BLANK,
               output logic H_BLANK);

// Get mode parameters
VideoModeParams_t mode_params;
assign mode_params = get_mode_params(mode_num);

// Counters (expanded to 11 bits for higher resolutions)
reg [10:0] hcount;
reg [10:0] vcount;

// Calculate blanking regions based on mode parameters
wire v_blank = vcount < mode_params.v_back_porch ||
               vcount >= (mode_params.v_back_porch + mode_params.v_active);
wire h_blank = hcount < mode_params.h_back_porch ||
               hcount >= (mode_params.h_back_porch + mode_params.h_active);

assign is_blank = v_blank | h_blank;
assign V_BLANK = v_blank;
assign H_BLANK = h_blank;

// Calculate sync pulse positions
// H sync: starts at h_total - h_sync_width, width based on mode
// V sync: starts at v_total - v_sync_width, width based on mode
wire [10:0] h_sync_width = mode_params.h_sync_end - mode_params.h_sync_start;
wire [10:0] v_sync_width = mode_params.v_sync_end - mode_params.v_sync_start;

// Sync signals - active low (negative polarity)
assign hsync = ~(hcount >= (mode_params.h_total - h_sync_width - mode_params.h_back_porch) &&
                 hcount < (mode_params.h_total - mode_params.h_back_porch));
assign vsync = ~(vcount >= (mode_params.v_total - v_sync_width - mode_params.v_back_porch) &&
                 vcount < (mode_params.v_total - mode_params.v_back_porch));

// Output current row/column within active area
assign row = v_blank ? 11'b0 : vcount - mode_params.v_back_porch;
assign col = h_blank ? 11'b0 : hcount - mode_params.h_back_porch;

// Timing counters
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        hcount <= 11'b0;
        vcount <= 11'b0;
    end else begin
        // Horizontal counter
        if (hcount == mode_params.h_total - 1'b1) begin
            hcount <= 11'd0;
            // Vertical counter increments at end of horizontal line
            if (vcount == mode_params.v_total - 1'b1)
                vcount <= 11'd0;
            else
                vcount <= vcount + 1'b1;
        end else begin
            hcount <= hcount + 1'b1;
        end
    end
end

endmodule
