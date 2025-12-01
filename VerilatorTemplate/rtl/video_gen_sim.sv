// Simple Video Signal Generator for Testing
// Generates VGA-style timing signals with test pattern
//
// Configurable resolution and timing parameters
// Default: 160x144 (Gameboy resolution)

`timescale 1ns / 1ps

module video_gen_sim #(
    parameter H_ACTIVE  = 160,    // Active pixels per line
    parameter H_FP      = 8,      // Horizontal front porch
    parameter H_SYNC    = 16,     // Horizontal sync width
    parameter H_BP      = 24,     // Horizontal back porch
    parameter V_ACTIVE  = 144,    // Active lines per frame
    parameter V_FP      = 3,      // Vertical front porch
    parameter V_SYNC    = 3,      // Vertical sync width
    parameter V_BP      = 15      // Vertical back porch
)(
    input  wire        clk,
    input  wire        reset,
    input  wire        enable,

    // VGA-style outputs
    output reg  [7:0]  vga_r,
    output reg  [7:0]  vga_g,
    output reg  [7:0]  vga_b,
    output reg         vga_hs,    // Horizontal sync (active low)
    output reg         vga_vs,    // Vertical sync (active low)
    output reg         vga_de,    // Data enable (active high)

    // Status
    output wire [10:0] pixel_x,
    output wire [10:0] pixel_y,
    output wire        frame_start
);

// Timing totals
localparam H_TOTAL = H_ACTIVE + H_FP + H_SYNC + H_BP;
localparam V_TOTAL = V_ACTIVE + V_FP + V_SYNC + V_BP;

// Counters
reg [10:0] h_count;
reg [10:0] v_count;

assign pixel_x = h_count;
assign pixel_y = v_count;
assign frame_start = (h_count == 0) && (v_count == 0);

// Horizontal and vertical counter
always @(posedge clk or posedge reset) begin
    if (reset) begin
        h_count <= 0;
        v_count <= 0;
    end else if (enable) begin
        if (h_count >= H_TOTAL - 1) begin
            h_count <= 0;
            if (v_count >= V_TOTAL - 1) begin
                v_count <= 0;
            end else begin
                v_count <= v_count + 1;
            end
        end else begin
            h_count <= h_count + 1;
        end
    end
end

// Generate sync signals
always @(posedge clk or posedge reset) begin
    if (reset) begin
        vga_hs <= 1;  // Inactive (high)
        vga_vs <= 1;  // Inactive (high)
        vga_de <= 0;
    end else begin
        // Horizontal sync (active during sync period)
        vga_hs <= !((h_count >= H_ACTIVE + H_FP) &&
                    (h_count < H_ACTIVE + H_FP + H_SYNC));

        // Vertical sync (active during sync period)
        vga_vs <= !((v_count >= V_ACTIVE + V_FP) &&
                    (v_count < V_ACTIVE + V_FP + V_SYNC));

        // Data enable (active during visible area)
        vga_de <= (h_count < H_ACTIVE) && (v_count < V_ACTIVE);
    end
end

// Generate test pattern
always @(posedge clk or posedge reset) begin
    if (reset) begin
        vga_r <= 0;
        vga_g <= 0;
        vga_b <= 0;
    end else if (vga_de) begin
        // Create a color pattern based on position
        // Horizontal color bars with vertical gradient

        // Divide screen into 8 vertical bars
        case (h_count[7:5])  // Top 3 bits for 8 regions
            3'd0: begin  // White
                vga_r <= 255;
                vga_g <= 255;
                vga_b <= 255;
            end
            3'd1: begin  // Yellow
                vga_r <= 255;
                vga_g <= 255;
                vga_b <= 0;
            end
            3'd2: begin  // Cyan
                vga_r <= 0;
                vga_g <= 255;
                vga_b <= 255;
            end
            3'd3: begin  // Green
                vga_r <= 0;
                vga_g <= 255;
                vga_b <= 0;
            end
            3'd4: begin  // Magenta
                vga_r <= 255;
                vga_g <= 0;
                vga_b <= 255;
            end
            3'd5: begin  // Red
                vga_r <= 255;
                vga_g <= 0;
                vga_b <= 0;
            end
            3'd6: begin  // Blue
                vga_r <= 0;
                vga_g <= 0;
                vga_b <= 255;
            end
            3'd7: begin  // Black
                vga_r <= 0;
                vga_g <= 0;
                vga_b <= 0;
            end
        endcase

        // Apply vertical gradient
        if (v_count < V_ACTIVE / 2) begin
            // Top half: full brightness
        end else begin
            // Bottom half: reduce brightness by position
            vga_r <= vga_r >> 1;
            vga_g <= vga_g >> 1;
            vga_b <= vga_b >> 1;
        end
    end else begin
        // Blanking - output black
        vga_r <= 0;
        vga_g <= 0;
        vga_b <= 0;
    end
end

endmodule
