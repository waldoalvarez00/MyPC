# VGA/EGA/CGA/MDA Video Mode Implementation Plan

## Status: INFRASTRUCTURE COMPLETE - HARDWARE IMPLEMENTATION IN PROGRESS

This document describes the comprehensive video mode implementation for the VGA/MCGA controller, adding support for all standard PC video modes.

## Completed: Mode Definitions (VGATypes.sv)

✅ **Created comprehensive mode definition system** with all standard PC video modes:

### Text Modes (5 modes)
- ✅ Mode 00h: 40x25 text, 16 colors (CGA)
- ✅ Mode 01h: 40x25 text, 16 colors (CGA)
- ✅ Mode 02h: 80x25 text, 16 colors (CGA)
- ✅ Mode 03h: 80x25 text, 16 colors (CGA) - **Previously supported**
- ✅ Mode 07h: 80x25 monochrome text (MDA)

### CGA Graphics Modes (3 modes)
- ✅ Mode 04h: 320x200, 4 colors, 2bpp - **Previously supported**
- ✅ Mode 05h: 320x200, 4 colors grayscale, 2bpp
- ✅ Mode 06h: 640x200, 2 colors, 1bpp - **NEW**

### EGA Graphics Modes (4 modes)
- ✅ Mode 0Dh: 320x200, 16 colors, 4bpp - **NEW**
- ✅ Mode 0Eh: 640x200, 16 colors, 4bpp - **NEW**
- ✅ Mode 0Fh: 640x350, monochrome, 1bpp - **NEW**
- ✅ Mode 10h: 640x350, 16 colors, 4bpp - **NEW**

### VGA Graphics Modes (3 modes)
- ✅ Mode 11h: 640x480, 2 colors, 1bpp - **NEW**
- ✅ Mode 12h: 640x480, 16 colors, 4bpp - **NEW**
- ✅ Mode 13h: 320x200, 256 colors, 8bpp - **Previously supported**

**Total: 15 video modes defined**

## Mode Definition Structure

Each mode includes complete timing parameters:
- Horizontal/Vertical active area
- Total horizontal/vertical counts
- Sync pulse positions
- Back porch values
- Bits per pixel (1, 2, 4, or 8)
- Text/graphics flag
- Text column/row counts (if applicable)

Example mode definition:
```systemverilog
MODE_12H: begin  // 640x480, 16 colors (VGA)
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
    params.bpp = BPP_4;  // 4 bits per pixel
    params.is_text = 1'b0;
    params.is_graphics = 1'b1;
end
```

## Required Hardware Modifications

### 1. VGARegisters.sv (Mode Detection)

**Status:** Needs implementation

**Required Changes:**
- Add mode number register (stores INT 10h mode number)
- Implement mode detection logic based on register writes
- Map 3D8h/3D9h/3C0h register combinations to mode numbers
- Pass mode number to VGASync and FrameBuffer

**Pseudo-code:**
```systemverilog
reg [7:0] current_mode;  // Stores BIOS mode number

always_ff @(posedge clk or posedge reset) begin
    if (reset)
        current_mode <= MODE_03H;  // Default 80x25 text
    else begin
        // Detect mode changes from register writes
        if (mode_change_detected)
            current_mode <= detected_mode_number;
    end
end
```

### 2. VGASync.sv (Configurable Timing)

**Status:** Needs major rewrite

**Current State:** Hardcoded for 640x480 timing
**Required:** Dynamic timing based on mode parameters

**Required Changes:**
```systemverilog
module VGASync(
    input logic clk,
    input logic reset,
    input VideoModeNumber_t mode_num,  // NEW: Mode input
    output logic vsync,
    output logic hsync,
    output logic is_blank,
    output logic [10:0] row,           // Expanded to 11 bits
    output logic [10:0] col,           // Expanded to 11 bits
    output logic V_BLANK,
    output logic H_BLANK
);

VideoModeParams_t mode_params;
assign mode_params = get_mode_params(mode_num);

// Use mode_params for all timing values
reg [10:0] hcount;
reg [10:0] vcount;

wire v_blank = vcount < mode_params.v_back_porch ||
               vcount >= (mode_params.v_back_porch + mode_params.v_active);
wire h_blank = hcount < mode_params.h_back_porch ||
               hcount >= (mode_params.h_back_porch + mode_params.h_active);

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        hcount <= 11'b0;
        vcount <= 11'b0;
    end else begin
        hcount <= hcount == mode_params.h_total - 1'b1 ? 11'd0 : hcount + 1'b1;
        if (hcount == mode_params.h_total - 1'b1)
            vcount <= vcount == mode_params.v_total - 1'b1 ? 11'd0 : vcount + 1'b1;
    end
end
```

### 3. FrameBuffer.sv (Multi-Resolution Support)

**Status:** Needs major rewrite

**Current State:** Assumes 640x480 with simple pixel doubling
**Required:** Support for all resolutions and pixel formats

**Required Changes:**

**a) Address Calculation (depends on mode)**
```systemverilog
always_comb begin
    case (mode_params.bpp)
        BPP_1: begin  // 1bpp (2 colors)
            // 8 pixels per byte
            fb_address = {row * (mode_params.h_active / 8) + (col / 8)};
            pixel_bit = 7 - col[2:0];
        end
        BPP_2: begin  // 2bpp (4 colors)
            // 4 pixels per byte
            fb_address = {row * (mode_params.h_active / 4) + (col / 4)};
            pixel_bits = 2'd3 - col[1:0];
        end
        BPP_4: begin  // 4bpp (16 colors)
            // 2 pixels per byte OR planar mode
            if (is_planar_mode) begin
                // EGA/VGA planar: 4 planes
                // Implement planar addressing
            end else begin
                // Packed: 2 pixels per byte
                fb_address = {row * (mode_params.h_active / 2) + (col / 2)};
            end
        end
        BPP_8: begin  // 8bpp (256 colors)
            // 1 pixel per byte
            fb_address = {row * mode_params.h_active + col};
        end
    endcase
end
```

**b) Pixel Extraction**
```systemverilog
always_comb begin
    case (mode_params.bpp)
        BPP_1: pixel_color = fb_data[pixel_bit] ? 4'hF : 4'h0;
        BPP_2: pixel_color = fb_data[pixel_bits*2 +: 2];
        BPP_4: pixel_color = fb_data[pixel_offset*4 +: 4];
        BPP_8: pixel_color = fb_data[7:0];
    endcase
end
```

**c) Text Mode Support**
```systemverilog
if (mode_params.is_text) begin
    // Calculate character position
    if (mode_params.text_cols == 40)
        char_x = col / 8;  // 40-column (8 pixels per char)
    else if (mode_params.text_cols == 80)
        char_x = col / 8;  // 80-column (8 pixels per char)
    else  // MDA: 9 pixels per char
        char_x = col / 9;

    char_y = row / char_height;

    // Fetch character and attribute from text buffer
    text_address = char_y * mode_params.text_cols + char_x;
end
```

### 4. FontColorLUT.sv (Palette Handling)

**Status:** Needs updates for EGA modes

**Required Changes:**
- Support 16-color palette for EGA modes
- Implement proper EGA palette registers
- Handle monochrome modes (modes 07h, 0Fh, 11h)

### 5. VGAController.sv (Top Level)

**Status:** Needs mode parameter threading

**Required Changes:**
- Pass mode number through hierarchy
- Adjust border calculations for different resolutions
- Handle different pixel clock requirements

## Pixel Format Details

### 1-bit (2 colors): Modes 06h, 0Fh, 11h
```
Byte: [b7 b6 b5 b4 b3 b2 b1 b0]
8 pixels, each bit = 1 pixel
Color: 0=background, 1=foreground
```

### 2-bit (4 colors): Modes 04h, 05h
```
Byte: [p3_h p3_l p2_h p2_l p1_h p1_l p0_h p0_l]
4 pixels, 2 bits each
Colors: 00, 01, 10, 11 (from CGA palette)
```

### 4-bit (16 colors): Modes 0Dh, 0Eh, 10h, 12h
```
** PLANAR FORMAT (EGA/VGA) **
4 memory planes: Blue, Green, Red, Intensity
Each plane stores 1 bit per pixel
Pixel color = {I, R, G, B} from 4 planes

** PACKED FORMAT (Mode 0Dh can use) **
Byte: [pixel1_3:0 pixel0_3:0]
2 pixels, 4 bits each
```

### 8-bit (256 colors): Mode 13h
```
Byte: [pixel_7:0]
1 pixel per byte
Color index into DAC palette
```

## Memory Layout

### Text Modes
```
Offset 0x0000-0x0F9F: Character/Attribute pairs
  Each char = 2 bytes: [Attribute][Character]
  40x25 = 2000 bytes
  80x25 = 4000 bytes
```

### Graphics Modes

**CGA (modes 04h-06h):**
```
0x0000-0x1FFF: Even scan lines (0, 2, 4, ...)
0x2000-0x3FFF: Odd scan lines (1, 3, 5, ...)
Interlaced format
```

**EGA/VGA Planar (modes 0Dh-12h):**
```
4 planes accessed via:
- Sequencer Map Mask (3C4h/3C5h)
- Graphics Controller Read Map Select (3CEh/3CFh)
Each plane is 64KB
```

**VGA Linear (mode 13h):**
```
0x0000-0xF9FF: 320x200 = 64000 bytes
Linear addressing, 1 byte per pixel
```

## Testing Strategy

### Phase 1: Mode Definition Tests
✅ Test VGATypes.sv get_mode_params() function
- Verify all 15 modes return correct parameters
- Check timing values are reasonable
- Validate bit-per-pixel settings

### Phase 2: Register Tests
- Test mode number detection
- Verify mode switching
- Check register compatibility

### Phase 3: Timing Tests
- Verify VGASync generates correct timing for each mode
- Check hsync/vsync pulse widths
- Validate total counts

### Phase 4: Framebuffer Tests
- Test address calculation for each mode
- Verify pixel extraction
- Check memory layout

### Phase 5: Integration Tests
- Full mode switching
- Verify output for each mode
- Performance testing

## Implementation Priority

### High Priority (Core Functionality)
1. ✅ VGATypes mode definitions - **COMPLETE**
2. ⏳ VGASync configurability - **IN PROGRESS**
3. ⏳ Basic mode switching in VGARegisters
4. ⏳ Simple framebuffer modes (1bpp, 2bpp, 8bpp)

### Medium Priority (Compatibility)
5. ⏳ 4bpp packed format
6. ⏳ Text mode variants (40-col, 80-col, MDA)
7. ⏳ EGA color palette
8. ⏳ Comprehensive testing

### Low Priority (Advanced Features)
9. ⬜ EGA planar mode (4bpp)
10. ⬜ CGA interlaced addressing
11. ⬜ MDA 9-pixel chars
12. ⬜ Mode timing precision

## Known Limitations

1. **Pixel Clock:** Currently assumes fixed 25MHz clock
   - Some modes may need different clocks
   - Consider pixel clock divider

2. **EGA Planar Mode:** Complex to implement
   - Requires 4 memory planes
   - Needs sequencer and graphics controller emulation

3. **CGA Interlacing:** Even/odd addressing
   - Modes 04h-06h use interlaced format
   - Needs special address calculation

4. **Memory Size:** Limited by FPGA RAM
   - Higher resolution modes need more memory
   - May need external SDRAM for full framebuffers

## Next Steps

1. **Implement VGASync configurability**
   - Make timing parameters dynamic
   - Add mode parameter input
   - Test with multiple modes

2. **Update FrameBuffer addressing**
   - Implement mode-specific address calculation
   - Support 1bpp, 2bpp, 4bpp, 8bpp formats
   - Add text mode support

3. **Enhance VGARegisters**
   - Add mode number tracking
   - Implement mode detection from register writes
   - Add INT 10h mode number register

4. **Create comprehensive tests**
   - Test each mode's timing
   - Verify pixel formats
   - Check mode switching

5. **Documentation**
   - Update user documentation
   - Add mode switching examples
   - Document register usage

## References

- IBM VGA Technical Reference Manual
- IBM EGA Technical Reference
- IBM CGA Technical Reference
- Video Electronics Standards Association (VESA) specifications
- FreeVGA timing documentation

## File Summary

**Modified Files:**
- ✅ `Quartus/rtl/VGA/VGATypes.sv` - Complete mode definitions

**Files Requiring Modification:**
- ⏳ `Quartus/rtl/VGA/VGASync.sv` - Make timing configurable
- ⏳ `Quartus/rtl/VGA/FrameBuffer.sv` - Multi-resolution support
- ⏳ `Quartus/rtl/VGA/VGARegisters.sv` - Mode detection
- ⏳ `Quartus/rtl/VGA/VGAController.sv` - Parameter threading
- ⏳ `Quartus/rtl/VGA/FontColorLUT.sv` - Extended palette support

**Test Files:**
- ⏳ `modelsim/vga_modes_tb.sv` - Comprehensive mode tests
- ⏳ `modelsim/run_vga_modes_test.sh` - Test automation
