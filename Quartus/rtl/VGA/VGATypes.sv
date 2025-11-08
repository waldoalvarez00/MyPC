// VGA/EGA/CGA/MDA Video Mode Definitions
// Comprehensive mode support for PC-compatible video

`ifndef VGA_TYPES_SV
`define VGA_TYPES_SV

// Video mode enumeration - covers all standard PC video modes
typedef enum logic [7:0] {
    // Text modes
    MODE_00H = 8'h00,  // 40x25 text, 16 colors
    MODE_01H = 8'h01,  // 40x25 text, 16 colors
    MODE_02H = 8'h02,  // 80x25 text, 16 colors
    MODE_03H = 8'h03,  // 80x25 text, 16 colors
    MODE_07H = 8'h07,  // 80x25 text, monochrome (MDA)

    // CGA graphics modes
    MODE_04H = 8'h04,  // 320x200, 4 colors
    MODE_05H = 8'h05,  // 320x200, 4 colors (gray)
    MODE_06H = 8'h06,  // 640x200, 2 colors

    // EGA graphics modes
    MODE_0DH = 8'h0D,  // 320x200, 16 colors
    MODE_0EH = 8'h0E,  // 640x200, 16 colors
    MODE_0FH = 8'h0F,  // 640x350, monochrome
    MODE_10H = 8'h10,  // 640x350, 16 colors

    // VGA graphics modes
    MODE_11H = 8'h11,  // 640x480, 2 colors
    MODE_12H = 8'h12,  // 640x480, 16 colors
    MODE_13H = 8'h13,  // 320x200, 256 colors (MCGA/VGA)

    MODE_UNKNOWN = 8'hFF
} VideoModeNumber_t;

// Video mode type categories
typedef enum logic [2:0] {
    MODE_TYPE_TEXT_40COL,      // 40-column text
    MODE_TYPE_TEXT_80COL,      // 80-column text
    MODE_TYPE_TEXT_MDA,        // Monochrome text
    MODE_TYPE_GRAPHICS_CGA,    // CGA graphics (320x200 or 640x200)
    MODE_TYPE_GRAPHICS_EGA,    // EGA graphics (various resolutions)
    MODE_TYPE_GRAPHICS_VGA,    // VGA graphics (640x480 or 320x200x256)
    MODE_TYPE_UNKNOWN
} VideoModeType_t;

// Color depth enumeration
typedef enum logic [2:0] {
    BPP_1  = 3'd0,  // 1 bit per pixel (2 colors)
    BPP_2  = 3'd1,  // 2 bits per pixel (4 colors)
    BPP_4  = 3'd2,  // 4 bits per pixel (16 colors)
    BPP_8  = 3'd3   // 8 bits per pixel (256 colors)
} BitsPerPixel_t;

// Video mode parameters structure
typedef struct packed {
    logic [10:0] h_active;      // Horizontal active pixels
    logic [10:0] v_active;      // Vertical active lines
    logic [10:0] h_total;       // Total horizontal (including blanking)
    logic [10:0] v_total;       // Total vertical (including blanking)
    logic [10:0] h_sync_start;  // H sync start
    logic [10:0] h_sync_end;    // H sync end
    logic [10:0] v_sync_start;  // V sync start
    logic [10:0] v_sync_end;    // V sync end
    logic [10:0] h_back_porch;  // H back porch
    logic [10:0] v_back_porch;  // V back porch
    BitsPerPixel_t bpp;         // Bits per pixel
    logic is_text;              // Text mode flag
    logic is_graphics;          // Graphics mode flag
    logic [6:0] text_cols;      // Text columns (if text mode)
    logic [5:0] text_rows;      // Text rows (if text mode)
} VideoModeParams_t;

// Function to get video mode parameters
function automatic VideoModeParams_t get_mode_params(input VideoModeNumber_t mode_num);
    VideoModeParams_t params;

    // Initialize all fields to zero (Icarus Verilog compatible)
    params.h_active = 11'd0;
    params.v_active = 11'd0;
    params.h_total = 11'd0;
    params.v_total = 11'd0;
    params.h_sync_start = 11'd0;
    params.h_sync_end = 11'd0;
    params.v_sync_start = 11'd0;
    params.v_sync_end = 11'd0;
    params.h_back_porch = 11'd0;
    params.v_back_porch = 11'd0;
    params.bpp = BPP_1;
    params.is_text = 1'b0;
    params.is_graphics = 1'b0;
    params.text_cols = 7'd0;
    params.text_rows = 6'd0;

    case (mode_num)
        // Mode 00h/01h: 40x25 text, 16 colors
        MODE_00H, MODE_01H: begin
            params.h_active = 11'd320;   // 40 chars * 8 pixels
            params.v_active = 11'd400;   // 25 chars * 16 scan lines
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_4;
            params.is_text = 1'b1;
            params.is_graphics = 1'b0;
            params.text_cols = 7'd40;
            params.text_rows = 6'd25;
        end

        // Mode 02h/03h: 80x25 text, 16 colors
        MODE_02H, MODE_03H: begin
            params.h_active = 11'd640;   // 80 chars * 8 pixels
            params.v_active = 11'd400;   // 25 chars * 16 scan lines
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_4;
            params.is_text = 1'b1;
            params.is_graphics = 1'b0;
            params.text_cols = 7'd80;
            params.text_rows = 6'd25;
        end

        // Mode 07h: MDA 80x25 monochrome text
        MODE_07H: begin
            params.h_active = 11'd720;   // MDA uses 9-pixel wide chars
            params.v_active = 11'd350;   // 25 chars * 14 scan lines
            params.h_total = 11'd900;
            params.v_total = 11'd440;
            params.h_sync_start = 11'd720;
            params.h_sync_end = 11'd810;
            params.v_sync_start = 11'd350;
            params.v_sync_end = 11'd352;
            params.h_back_porch = 11'd90;
            params.v_back_porch = 11'd88;
            params.bpp = BPP_1;
            params.is_text = 1'b1;
            params.is_graphics = 1'b0;
            params.text_cols = 7'd80;
            params.text_rows = 6'd25;
        end

        // Mode 04h/05h: 320x200, 4 colors (CGA)
        MODE_04H, MODE_05H: begin
            params.h_active = 11'd320;
            params.v_active = 11'd200;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_2;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 06h: 640x200, 2 colors (CGA high-res)
        MODE_06H: begin
            params.h_active = 11'd640;
            params.v_active = 11'd200;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_1;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 0Dh: 320x200, 16 colors (EGA)
        MODE_0DH: begin
            params.h_active = 11'd320;
            params.v_active = 11'd200;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_4;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 0Eh: 640x200, 16 colors (EGA)
        MODE_0EH: begin
            params.h_active = 11'd640;
            params.v_active = 11'd200;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_4;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 0Fh: 640x350, monochrome (EGA)
        MODE_0FH: begin
            params.h_active = 11'd640;
            params.v_active = 11'd350;
            params.h_total = 11'd800;
            params.v_total = 11'd449;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd387;
            params.v_sync_end = 11'd389;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd60;
            params.bpp = BPP_1;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 10h: 640x350, 16 colors (EGA)
        MODE_10H: begin
            params.h_active = 11'd640;
            params.v_active = 11'd350;
            params.h_total = 11'd800;
            params.v_total = 11'd449;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd387;
            params.v_sync_end = 11'd389;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd60;
            params.bpp = BPP_4;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 11h: 640x480, 2 colors (VGA)
        MODE_11H: begin
            params.h_active = 11'd640;
            params.v_active = 11'd480;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_1;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 12h: 640x480, 16 colors (VGA)
        MODE_12H: begin
            params.h_active = 11'd640;
            params.v_active = 11'd480;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_4;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        // Mode 13h: 320x200, 256 colors (MCGA/VGA)
        MODE_13H: begin
            params.h_active = 11'd320;
            params.v_active = 11'd200;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_8;
            params.is_text = 1'b0;
            params.is_graphics = 1'b1;
        end

        default: begin
            // Default to mode 03h (80x25 text)
            params.h_active = 11'd640;
            params.v_active = 11'd400;
            params.h_total = 11'd800;
            params.v_total = 11'd525;
            params.h_sync_start = 11'd656;
            params.h_sync_end = 11'd752;
            params.v_sync_start = 11'd490;
            params.v_sync_end = 11'd492;
            params.h_back_porch = 11'd48;
            params.v_back_porch = 11'd33;
            params.bpp = BPP_4;
            params.is_text = 1'b1;
            params.is_graphics = 1'b0;
            params.text_cols = 7'd80;
            params.text_rows = 6'd25;
        end
    endcase

    return params;
endfunction

// Legacy compatibility function (used by existing code)
typedef enum bit [1:0] {
    VIDEO_MODE_TEXT,
    VIDEO_MODE_4_COLOR,
    VIDEO_MODE_256_COLOR
} VideoMode_t;

function VideoMode_t get_video_mode;
    input logic graphics_enabled;
    input logic vga_256_color;

    if (vga_256_color)
        get_video_mode = VIDEO_MODE_256_COLOR;
    else if (graphics_enabled)
        get_video_mode = VIDEO_MODE_4_COLOR;
    else
        get_video_mode = VIDEO_MODE_TEXT;
endfunction

`endif // VGA_TYPES_SV
