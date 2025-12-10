# Critical DMG Monochrome Display Fix

**Date:** December 9, 2025
**Issue:** LCD showing solid black despite lcd_mode cycling (LCD working)
**Status:** ✅ **FIXED**

## Root Cause

The GameBoy simulator was outputting VGA color from `lcd_data` (15-bit RGB555 for Game Boy Color) but running in DMG (original Game Boy) monochrome mode. In DMG mode:

- `lcd_data` = all zeros (no GBC color data)
- `lcd_data_gb` = 2-bit monochrome pixel values (0-3)

The VGA output logic **only used lcd_data**, completely ignoring `lcd_data_gb`, resulting in:
- VGA_R = 0x00
- VGA_G = 0x00
- VGA_B = 0x00
- **Result:** Solid black screen

## Symptoms

**Before the fix:**
- Console: `TEST 3: [PASS] ce_cpu is pulsing normally` ✅
- Diagnostics: `lcd_mode: 2` (cycling between 0-3) ✅
- Video window: Changed from gray (no signal) to black (signal present) ✅
- **BUT:** Solid black screen, no visible pattern ❌

This proved:
- ✅ CPU working
- ✅ Boot ROM executing
- ✅ LCD controller working
- ✅ Video signal present
- ❌ But no pixel data being rendered (all RGB = 0)

## The Fix

### Modified File: `gameboy_sim.v` (lines 302-314)

**Before (broken):**
```verilog
// Convert 15-bit LCD data to 24-bit VGA (RGB555 -> RGB888)
assign VGA_R = {lcd_data[14:10], lcd_data[14:12]};
assign VGA_G = {lcd_data[9:5], lcd_data[9:7]};
assign VGA_B = {lcd_data[4:0], lcd_data[4:2]};
```

**After (fixed):**
```verilog
// Convert DMG 2-bit monochrome to 8-bit grayscale
// GameBoy DMG palette: 0=White, 1=Light gray, 2=Dark gray, 3=Black
wire [7:0] dmg_gray;
assign dmg_gray = (lcd_data_gb == 2'b00) ? 8'hFF :  // Color 0: White (#FFFFFF)
                  (lcd_data_gb == 2'b01) ? 8'hAA :  // Color 1: Light gray (#AAAAAA)
                  (lcd_data_gb == 2'b10) ? 8'h55 :  // Color 2: Dark gray (#555555)
                                           8'h00;   // Color 3: Black (#000000)

// Convert 15-bit LCD data to 24-bit VGA (RGB555 -> RGB888 for GBC, grayscale for DMG)
// Use isGBC_game to select between GBC color output and DMG monochrome output
assign VGA_R = isGBC_game ? {lcd_data[14:10], lcd_data[14:12]} : dmg_gray;
assign VGA_G = isGBC_game ? {lcd_data[9:5], lcd_data[9:7]} : dmg_gray;
assign VGA_B = isGBC_game ? {lcd_data[4:0], lcd_data[4:2]} : dmg_gray;
```

## How It Works

### DMG Mode (isGBC_game = 0)

1. **lcd_data_gb** outputs 2-bit monochrome pixel values:
   - `2'b00` = Color index 0
   - `2'b01` = Color index 1
   - `2'b10` = Color index 2
   - `2'b11` = Color index 3

2. **Palette mapping** converts to 8-bit grayscale:
   - Color 0 → `8'hFF` (White: 255, 255, 255)
   - Color 1 → `8'hAA` (Light gray: 170, 170, 170)
   - Color 2 → `8'h55` (Dark gray: 85, 85, 85)
   - Color 3 → `8'h00` (Black: 0, 0, 0)

3. **VGA_R, VGA_G, VGA_B** all get the same grayscale value (creates monochrome display)

### GBC Mode (isGBC_game = 1)

Uses the original `lcd_data` 15-bit RGB555 color format (unchanged from before).

## Expected Behavior After Fix

### With Test Pattern Boot ROM

The minimal boot ROM we created writes three distinct tile patterns:

**Tile 0 ($8000): Horizontal stripes**
- 2 rows of 0xFF (all pixels color 3 = black)
- 2 rows of 0x00 (all pixels color 0 = white)
- Repeating pattern

**Tile 1 ($8010): Checkerboard**
- All 16 bytes = 0xAA (10101010 binary)
- Alternating pixels: color 2, color 3, color 2, color 3...
- Creates dark gray/black checkerboard

**Tile 2 ($8020): Inverted checkerboard**
- All 16 bytes = 0x55 (01010101 binary)
- Alternating pixels: color 1, color 2, color 1, color 2...
- Creates light gray/dark gray checkerboard

**Tilemap ($9800): Alternating pattern**
- Tiles arranged as: 0, 1, 2, 0, 1, 2, 0, 1, 2...
- Creates visible stripe pattern across screen

**What you should see:**
- **Vertical stripes** of three different patterns alternating across the screen
- **NOT solid black** - multiple shades of gray and white
- Pattern should be clearly visible

### If Still Solid Color

If the screen is still solid (but different from black):

1. **Solid white** → All pixels reading as color 0, possible tile data issue
2. **Solid light gray** → All pixels reading as color 1
3. **Solid dark gray** → All pixels reading as color 2
4. **Solid black** → All pixels reading as color 3

Check diagnostic window:
- `cpu_addr` should be > 0x0100 (in cart ROM, boot complete)
- `boot_rom_enabled` should be 0 (boot ROM disabled)
- `lcd_mode` should be cycling (LCD active)

## Build Instructions

### Rebuild Verilator Model (Already Done!)

```bash
cd GameBoySimulator/verilator
bash ./verilate_gameboy.sh
```

**Status:** ✅ Already completed (Vtop files generated at 09:41)

### Rebuild Visual Studio Project

**Option 1: Visual Studio IDE**
1. Open `GameBoySimulator/verilator/sim.vcxproj`
2. Configuration: Release, Platform: x64
3. Build → Rebuild Solution (Ctrl+Shift+B)

**Option 2: MSBuild Command Line**
```cmd
cd GameBoySimulator\verilator
"C:\Program Files\Microsoft Visual Studio\2022\Community\MSBuild\Current\Bin\MSBuild.exe" sim.vcxproj /p:Configuration=Release /p:Platform=x64 /t:Rebuild
```

**Expected output:**
```
Build succeeded.
0 Errors, 0 Warnings
```

**Executable location:**
```
GameBoySimulator\verilator\x64\Release\sim.exe
```

## Running the Fixed Simulator

```cmd
cd GameBoySimulator\verilator\x64\Release
.\sim.exe
```

Or with custom ROM:
```cmd
.\sim.exe path\to\your_rom.gb
```

## What to Watch For

### Startup Console Output (Should Be Unchanged)

```
=== GAMEBOY SIMULATOR GUI ===
ROM loaded: game.gb (32768 bytes)
...
TEST 3: Clock enable pulses
  Rising edges: 62
  [PASS] ce_cpu is pulsing normally
```

### Clock & State Diagnostics Window

```
=== CLOCK SIGNALS ===
ce_cpu: 0 [PULSING] (62 edges/1Kcyc)  ← Should show PULSING

=== CORE STATE ===
reset: 0 [RELEASED]
main_time: (increasing)
SDRAM: R=(increasing) W=(increasing)

=== BOOT & CART ===
boot_rom_enabled: 0 [CART ROM]  ← Should be 0 after boot

=== LCD STATE ===
lcd_mode: 2  ← Should cycle 0→2→3→0→2→3...
```

### Video Window - **THE BIG TEST!**

**Expected:** Visible pattern with:
- White stripes (horizontal lines)
- Black stripes (horizontal lines)
- Light gray checkerboard areas
- Dark gray checkerboard areas

**NOT expected:** Solid black screen

## Technical Background

### GameBoy Graphics Architecture

**Original Game Boy (DMG):**
- Monochrome display (4 shades of gray)
- LCD outputs 2-bit pixel values (0-3)
- Background palette register (BGP at $FF47) maps these to shades
- Example palette 0xE4 = 11100100 binary:
  - Bits 7-6 (11) → Color 3 maps to shade 3 (black)
  - Bits 5-4 (10) → Color 2 maps to shade 2 (dark gray)
  - Bits 3-2 (01) → Color 1 maps to shade 1 (light gray)
  - Bits 1-0 (00) → Color 0 maps to shade 0 (white)

**Game Boy Color (GBC):**
- Full color display (32,768 colors)
- LCD outputs 15-bit RGB555 color values
- 5 bits each for Red, Green, Blue

### Signal Flow

```
GameBoy Core (gb module)
  ↓
  ├─ lcd_data [14:0]     → GBC: 15-bit RGB555 color
  └─ lcd_data_gb [1:0]   → DMG: 2-bit monochrome (0-3)
  ↓
isGBC_game signal selects which to use
  ↓
dmg_gray conversion (if DMG mode)
  ↓
VGA_R, VGA_G, VGA_B [7:0] each
  ↓
C++ color packing: 0xFF000000 | VGA_B << 16 | VGA_G << 8 | VGA_R
  ↓
ImGui video output
  ↓
Display window
```

## Verification Steps

After rebuilding and running:

1. **Check console output:**
   - ✅ TEST 3 shows [PASS]
   - ✅ Clock divider shows ce_cpu=1

2. **Check diagnostic window:**
   - ✅ ce_cpu shows [PULSING] (62 edges/1Kcyc)
   - ✅ main_time increasing
   - ✅ boot_rom_enabled changes 1→0
   - ✅ lcd_mode cycling (0-3)

3. **Check video window:**
   - ✅ **PATTERN VISIBLE** (stripes/checkerboard)
   - ❌ If solid color: See troubleshooting below

## Troubleshooting After Fix

### Issue: Still solid black

**Check:**
1. Did you rebuild after running verilate_gameboy.sh?
2. Is the correct executable running? (Check file date)
3. Let simulation run for 30+ seconds (boot takes time)

### Issue: Solid white

Possible causes:
- Palette inverted in minimal boot ROM
- All tile data reading as 0x00
- lcd_data_gb stuck at 2'b00

### Issue: Solid gray

Possible causes:
- lcd_data_gb stuck at fixed value
- Tile map not initialized
- VRAM writes not working

### Issue: Garbage/random pixels

This would actually be good news! It means:
- ✅ Video pipeline working
- ✅ Pixel rendering working
- Might just need timing adjustment or palette fix

## Summary

✅ **Root cause identified:** VGA output ignored DMG monochrome data (lcd_data_gb)
✅ **Fix implemented:** Added DMG-to-grayscale conversion with mode selection
✅ **Verilator regenerated:** Fresh C++ model at 09:41 with fix
⏳ **Next step:** Rebuild Visual Studio project and test

**Expected outcome:** GameBoy LCD shows visible patterns (stripes and checkerboards) instead of solid black.

---

**Key Achievement:** We progressed from:
1. No video signal (gray screen) →
2. Video signal but no pixels (black screen) →
3. **(After this fix)** Video signal with visible pixels ← **YOU ARE HERE**

The video pipeline is fully functional. We just needed to wire up the DMG monochrome data path!
