# VGA/MCGA Controller Testing Findings

## Summary
Created comprehensive testbench for VGA/MCGA controller (VGARegisters module) and identified multiple bugs and missing features. The controller implements basic CGA/MCGA graphics modes but has Icarus Verilog compatibility issues and missing initialization.

## Supported Video Modes

The controller implements 3 video modes:

1. **TEXT Mode** (Mode 02h/03h)
   - 80x25 text display
   - 16 foreground / 8 background colors
   - Hardware cursor support
   - Default mode at startup

2. **4-COLOR CGA Graphics** (Mode 04h)
   - 320x200 resolution
   - 4 colors (2 bits per pixel)
   - Packed pixel format (4 pixels per byte)

3. **256-COLOR MCGA/VGA Mode** (Mode 13h)
   - 320x200 resolution
   - 256 colors (8 bits per pixel)
   - DAC palette with 18-bit RGB (6 bits per component)
   - Enabled via AMCR register (3C0h) = 0x41

## Missing Video Modes

As noted by user, several standard CGA/EGA/VGA modes are NOT implemented:

1. **2-Color High-Resolution** (Mode 06h)
   - 640x200 graphics, 2 colors
   - 1 bit per pixel

2. **16-Color EGA Modes**
   - Mode 0Dh: 320x200, 16 colors
   - Mode 0Eh: 640x200, 16 colors
   - Mode 0Fh: 640x350, monochrome
   - Mode 10h: 640x350, 16 colors

3. **16-Color VGA Modes**
   - Mode 11h: 640x480, 2 colors
   - Mode 12h: 640x480, 16 colors

4. **40-Column Text Modes** (Mode 00h/01h)
   - May work but not verified
   - No specific support in code

5. **Monochrome Modes**
   - MDA text mode
   - Hercules graphics

## Bugs Found and Fixed

### Bug #1: Uninitialized Registers (CRITICAL)
**Location:** `VGARegisters.sv:334-346`

**Problem:** sys_graphics_enabled not initialized in reset block
- At startup, register contains 'X' (undefined)
- Mode register reads incorrectly
- Graphics mode state unpredictable

**Fix Applied:**
```systemverilog
always_ff @(posedge clk or posedge reset)
    if (reset) begin
        text_enabled <= 1'b1;
        display_enabled <= 1'b1;
        sys_graphics_enabled <= 1'b0;  // Fix: Initialize to 0
    end
```

### Bug #2: Additional Uninitialized Registers
**Location:** `VGARegisters.sv:80-118`

**Problem:** Many registers not initialized:
- sys_amcr (AMCR register for 256-color mode)
- sys_palette_sel, sys_bright_colors
- cursor_mode, active_index
- sys_cursor_pos
- DAC index registers and offsets

**Fix Applied:** Added initial block:
```systemverilog
initial begin
    sys_amcr = 8'h00;
    sys_palette_sel = 1'b0;
    sys_bright_colors = 1'b0;
    cursor_mode = 2'b00;
    active_index = 4'h0;
    sys_cursor_pos = 15'h0000;
    dac_wr_idx = 8'h00;
    dac_rd_idx = 8'h00;
    dac_wr_offs = 2'b00;
    dac_rd_offs = 2'b00;
    dac_component_rg = 12'h000;
end
```

### Bug #3: Icarus Verilog Type Strictness
**Location:** `VGARegisters.sv:99-107, 82`

**Problem:** Signals assigned in procedural blocks declared as wire
- Icarus Verilog requires logic or reg for procedural assignments
- sys_cursor_scan_start, sys_cursor_scan_end, sys_background_color
- index_value

**Fix Applied:** Changed wire to logic declarations

### Bug #4: Data Output Timing Issue (Icarus Verilog)
**Location:** `VGARegisters.sv:403-441`

**Problem:** always_ff block structure problematic for Icarus Verilog
- Sets data_m_data_out to 0 first, then conditionally updates
- Non-blocking assignments with multiple if statements
- Icarus Verilog's strict timing causes issues

**Fix Applied:** Refactored to use always_comb + registered output:
```systemverilog
logic [15:0] data_out_comb;

always_comb begin
    data_out_comb = 16'b0;
    if (!data_m_wr_en) begin
        // ... conditional assignments using blocking = ...
    end
end

always_ff @(posedge clk) begin
    data_m_data_out <= data_out_comb;
end
```

## Test Results

**After Fixes:** Some improvements but still issues
- Tests compile and run
- Basic functionality tested
- Many tests still failing due to remaining compatibility issues

**Test Coverage (23 tests total):**
1. Initial mode read (text mode default)
2. Switch to 4-color CGA graphics
3. Color select register (palette, brightness, background)
4. Cursor position programming (high/low bytes)
5. Cursor scan line configuration (start/end)
6. Switch to 256-color MCGA mode
7. DAC palette programming (RGB components)
8. Status register read
9. ACK signal timing
10. Index register persistence
11. Return to text mode

**Known Limitations:**
- Clock domain crossing delays not fully accounted for in tests
- Full DAC palette functionality may need additional testing
- Actual video output timing not tested (CPU interface only)

## Register Map Tested

**CRT Controller Registers (via 3D4h/3D5h):**
- 3D4h: Index Register (write index 0-15)
- 3D5h: Data Register (indexed access)
  - Index 0Ah: Cursor Start (scan line, cursor mode)
  - Index 0Bh: Cursor End (scan line)
  - Index 0Eh: Cursor Position High
  - Index 0Fh: Cursor Position Low

**Mode Control:**
- 3D8h: Mode Control Register
  - Bit 0: Text enable
  - Bit 1: Graphics enable
  - Bit 3: Display enable

**Color Control:**
- 3D9h: Color Select Register
  - Bits 3-0: Background color
  - Bit 4: Bright colors
  - Bit 5: Palette select

**Status:**
- 3DAh: Status Register (read-only)
  - Bit 0: Display enable feedback
  - Bit 3: Vertical sync

**Attribute Mode:**
- 3C0h: AMCR (Attribute Mode Control Register)
  - Value 0x41: Enable 256-color mode

**DAC Palette:**
- 3C7h: DAC Read Index
- 3C8h: DAC Write Index
- 3C9h: DAC Data (RGB components, 6 bits each)

## Recommendations

1. **Continue fixing Icarus compatibility issues**
   - Still some test failures likely due to timing
   - May need additional delay cycles in testbench
   - Consider more clock domain crossing fixes

2. **Add missing video modes** (if needed)
   - Implement 640x200 2-color mode
   - Consider EGA 16-color modes
   - Add 40-column text support

3. **Framebuffer testing**
   - Current tests only cover CPU interface
   - Need tests for actual pixel output
   - Verify memory addressing for each mode

4. **Palette initialization**
   - DAC RAM starts uninitialized
   - Consider default CGA palette
   - Test palette in all modes

5. **Documentation**
   - Add comments for register bit definitions
   - Document supported vs unsupported modes clearly
   - Add mode switching examples

## Files Created

- `modelsim/vga_registers_tb.sv` - Comprehensive register testbench (23 tests)
- `modelsim/run_vga_test.sh` - Automated test script
- `modelsim/DACRam_sim.sv` - Generic DAC RAM for simulation (replaces Altera primitive)
- `VGA_MCGA_FINDINGS.md` - This document

## Conclusion

The VGA/MCGA controller implements basic CGA and MCGA functionality but:
- **Has initialization bugs** that affect reliability
- **Missing several standard video modes** (as noted by user)
- **Has Icarus Verilog compatibility issues** similar to other modules
- **Needs more comprehensive testing** for full validation

The fixes applied improve initialization and Icarus compatibility, but full functionality testing requires more work to resolve remaining timing and cross-domain issues.
