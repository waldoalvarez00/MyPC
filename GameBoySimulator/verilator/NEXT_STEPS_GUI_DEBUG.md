# Next Steps - GUI DMG Debug

**Date:** December 9, 2025
**Status:** ✅ Segfault fixed, DMG conversion confirmed working

---

## Summary

The headless test segfault has been fixed and **confirmed that the DMG grayscale conversion DOES work**:

```
Test output:
  dbg_isGBC_game: 0     ← DMG mode (correct)
  dbg_lcd_data_gb: 0    ← Color 0 (white in palette 0xE4)
  VGA_R: 255            ← WHITE!
  VGA_G: 255
  VGA_B: 255            ← Conversion working!
```

When `lcd_data_gb = 0`, the VGA outputs 255,255,255 (white), proving the Verilog DMG conversion logic is correct.

---

## What You Need To Do (Windows)

### Step 1: Rebuild Visual Studio Project

The Verilator model has been regenerated with the DMG fix. You need to rebuild the GUI simulator:

```cmd
cd C:\Users\waldo\Documents\GitHub\MyPC\GameBoySimulator\verilator

"C:\Program Files\Microsoft Visual Studio\2022\Community\MSBuild\Current\Bin\MSBuild.exe" sim.vcxproj /p:Configuration=Release /p:Platform=x64 /t:Rebuild
```

### Step 2: Run and Check New Diagnostics

Run the GUI simulator:
```cmd
cd x64\Release
.\sim.exe
```

### Step 3: Check DMG Debug Section

In the diagnostic window, you'll now see a new section:

```
=== DMG DEBUG ===
Mode: DMG (mono)  or  GBC (color)
lcd_data: 0x____ (RGB555)
lcd_data_gb: _ (DMG 0-3)
VGA RGB: (_,_,_)
```

**What to report:**
1. **Mode:** Should show "DMG (mono)" for game.gb
2. **lcd_data_gb:** What value does this show? (should be 0-3)
3. **VGA RGB:** What values? (currently showing 0,0,0 = black)

---

## Diagnosis Guide

Based on the new debug output, we can determine the issue:

### Case 1: Mode shows "GBC (color)"
**Problem:** isGBC_game incorrectly set to 1
**Why:** Bypasses DMG grayscale conversion
**Fix:** Check cart ROM header byte 0x143 (GBC flag)

### Case 2: Mode shows "DMG (mono)", lcd_data_gb always 0
**Problem:** Correct mode but always outputting color 0
**Expected:** With palette 0xE4 and tile data 0xFF/0x00, should vary 0-3
**Actual:** If always 0, VRAM writes might not reach LCD or timing issue

### Case 3: Mode shows "DMG (mono)", lcd_data_gb always 3
**Problem:** All pixels reading as black
**Why:** Palette or VRAM data issue
**Check:** Boot ROM tile writes to $8000-$8010

### Case 4: Mode shows "DMG (mono)", lcd_data_gb varies 0-3
**GOOD!** Conversion working correctly
**If still black on screen:** C++ video rendering issue (sim_video.cpp)

---

## Expected vs Actual

### Expected (Working DMG Conversion):
```
Mode: DMG (mono)
lcd_data: 0x0000 (not used in DMG mode)
lcd_data_gb: 0-3 (varies during pixel output)
VGA RGB: (255,255,255) when lcd_data_gb=0
VGA RGB: (170,170,170) when lcd_data_gb=1
VGA RGB: (85,85,85) when lcd_data_gb=2
VGA RGB: (0,0,0) when lcd_data_gb=3
```

### Current (GUI Still Black):
```
Mode: ??? (need to check)
lcd_data_gb: ??? (need to check)
VGA RGB: (0,0,0) ← all black
```

---

## Files Modified

### Verilator Model (Linux):
- `gameboy_sim.v` - DMG conversion + debug signals
- `obj_dir/` - Fresh Verilator build (December 9, 12:20)

### GUI Simulator (Windows):
- `sim_main_gui.cpp` - Added DMG DEBUG section to diagnostic window
- **Action Required:** Rebuild Visual Studio project

---

## Technical Notes

### DMG Grayscale Conversion (gameboy_sim.v lines 304-316):

```verilog
wire [7:0] dmg_gray;
assign dmg_gray = (lcd_data_gb == 2'b00) ? 8'hFF :  // 0 → White
                  (lcd_data_gb == 2'b01) ? 8'hAA :  // 1 → Light gray
                  (lcd_data_gb == 2'b10) ? 8'h55 :  // 2 → Dark gray
                                           8'h00;   // 3 → Black

assign VGA_R = isGBC_game ? {lcd_data[14:10], lcd_data[14:12]} : dmg_gray;
assign VGA_G = isGBC_game ? {lcd_data[9:5], lcd_data[9:7]} : dmg_gray;
assign VGA_B = isGBC_game ? {lcd_data[4:0], lcd_data[4:2]} : dmg_gray;
```

### Headless Test Confirmation:

The minimal test (`test_lcd_minimal.cpp`) proves this logic works:
- Input: `isGBC_game=0, lcd_data_gb=0`
- Output: `VGA_R=255, VGA_G=255, VGA_B=255` ✓

---

## Troubleshooting

### If Mode Shows "GBC (color)":

The cart ROM might have GBC flag set. Check byte 0x143:
- `0x00` or `0xFF` = DMG only
- `0x80` = GBC compatible
- `0xC0` = GBC only

If using `game.gb`, this should be `0x00` (DMG).

### If lcd_data_gb Always Same Value:

This suggests either:
1. LCD controller not reading from VRAM correctly
2. VRAM not written by boot ROM
3. Palette register configured incorrectly

The boot ROM should:
1. Write palette 0xE4 to $FF47
2. Write tile data to $8000-$8010
3. Write tilemap to $9800
4. Enable LCD with $91 to $FF40

### If VGA RGB Values Don't Match Expected:

With DMG mode and varying lcd_data_gb:
- `lcd_data_gb=0` should give RGB=(255,255,255)
- `lcd_data_gb=1` should give RGB=(170,170,170)
- `lcd_data_gb=2` should give RGB=(85,85,85)
- `lcd_data_gb=3` should give RGB=(0,0,0)

If all showing (0,0,0), either:
- lcd_data_gb is always 3
- Mode is actually GBC and lcd_data is 0

---

## Success Criteria

✅ **Working:** When you see varying VGA RGB values matching the lcd_data_gb conversion table above

❌ **Still Broken:** If diagnostic shows correct mode but VGA RGB doesn't match expected values

---

## If Still Black After This

If the diagnostic shows:
```
Mode: DMG (mono)
lcd_data_gb: 3 (or any fixed value)
VGA RGB: (0,0,0)
```

Then the issue is in the GameBoy core's LCD controller or VRAM. We'll need to:
1. Verify VRAM contents were written by boot ROM
2. Check LCD controller is reading from VRAM correctly
3. Verify palette register is configured
4. Check timing between CPU writes and LCD reads

But first, **please rebuild and report what the DMG DEBUG section shows!**
