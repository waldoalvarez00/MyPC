# GameBoy LCD Black Screen - Final Diagnosis

**Date:** December 9, 2025
**Status:** ✅ Root Cause Identified

---

## TL;DR - The Problem

Your GameBoy GUI simulator shows a black screen because **VRAM is never initialized**. The LCD controller reads VRAM as all zeros, so every pixel is color 0.

- **Headless test:** Color 0 → WHITE (255,255,255) ✓ DMG conversion works!
- **Your GUI:** Color 0 → BLACK (0,0,0) ← Different palette or rendering

**Root Cause:** Boot ROM executes correctly, but VRAM writes are **blocked or not persisting**.

---

## What I Discovered

### Comprehensive Diagnostic Test Results

I ran detailed tests that monitored every aspect of the LCD pipeline:

**Test: `test_lcd_diagnostics.cpp`**
- ✅ CPU running (212,486 ce_cpu pulses over 3.4M cycles)
- ✅ LCD active (3 complete frames rendered)
- ✅ isGBC_game = 0 (correct DMG mode)
- ✅ VGA outputs WHITE (255,255,255)
- ❌ **lcd_data_gb = 0 (NEVER changes!)**

```
lcd_data_gb distribution across 3.4 million cycles:
  Color 0: 3,399,768 samples (100.0%)
  Color 1: 0 samples
  Color 2: 0 samples
  Color 3: 0 samples
```

**Test: `test_vram_writes.cpp`**
- ❌ Only 1 VRAM access detected (expected 4+)
- Boot ROM should write pattern to $8000-$8003
- Writes are not reaching VRAM or being blocked

---

## Why DMG Conversion Shows WHITE (Not Black)

The DMG grayscale conversion is **working perfectly**:

```verilog
// gameboy_sim.v lines 304-316
assign dmg_gray = (lcd_data_gb == 2'b00) ? 8'hFF :  // 0 → White (255)
                  (lcd_data_gb == 2'b01) ? 8'hAA :  // 1 → Light gray (170)
                  (lcd_data_gb == 2'b10) ? 8'h55 :  // 2 → Dark gray (85)
                                           8'h00;   // 3 → Black (0)
```

When `lcd_data_gb = 0` → `VGA_R/G/B = 255` (WHITE)

The headless test confirms this is working correctly. Every pixel outputs as white because lcd_data_gb is always 0.

---

## Why Your GUI Shows BLACK (Different Result)

The headless test shows WHITE, but you report BLACK in your GUI. Possible reasons:

### Hypothesis 1: Different Palette Register
The GUI's `game.gb` ROM might:
- Have inverted palette (0x1B instead of 0xE4)
- Set palette differently than test boot ROM
- Have different Boot ROM that sets different palette

### Hypothesis 2: C++ Video Rendering
The GUI's `sim_video.cpp` might:
- Invert the RGB values (255 - value)
- Apply additional color processing
- Have palette lookup table in software

### Hypothesis 3: GBC Mode Detection
If isGBC_game is incorrectly set to 1:
- Would bypass DMG grayscale conversion
- Would use lcd_data (RGB555) = 0x0000 → (0,0,0) black

---

## The Real Problem: VRAM Not Initialized

**Why lcd_data_gb is stuck at 0:**

GameBoy LCD pixel pipeline:
1. Read tilemap entry → tile index
2. Read tile data from VRAM → 2-bit pixel values
3. Look up in palette → color index (lcd_data_gb)
4. DMG conversion → 8-bit grayscale

If VRAM is all zeros:
- Tile 0 = 16 bytes of 0x00
- Every pixel = 2 bits of 0b00
- lcd_data_gb = 0 (always)
- Result: Solid color (white in test, black in GUI)

**Why VRAM is all zeros:**

GameBoy VRAM is only writable when:
1. LCD is disabled (LCDC bit 7 = 0), OR
2. LCD is NOT in mode 3 (pixel transfer)

Boot ROM should:
1. Turn OFF LCD (write 0x00 to $FF40)
2. Write tile data to $8000-$8FFF
3. Write tilemap to $9800-$9BFF
4. Turn ON LCD (write 0x91 to $FF40)

But VRAM write test shows **only 1 access** instead of expected 4+.

---

## What This Means for Your GUI

After you rebuild the Visual Studio project with the new Verilator model, you should see:

### Expected Diagnostic Output:

```
=== DMG DEBUG ===
Mode: DMG (mono)          ← Correct
lcd_data: 0x0000          ← Correct (not used in DMG mode)
lcd_data_gb: 0            ← STUCK AT 0 (problem!)
VGA RGB: (0,0,0)          ← Black (your current result)
```

If you see:
- `lcd_data_gb: 0` (constant) → VRAM not initialized ✓ Confirmed
- `VGA RGB: (0,0,0)` → Your palette/rendering makes 0 → black
- `Mode: GBC (color)` → Different issue (mode detection)

---

## Next Steps

### Step 1: Confirm Diagnosis in GUI

Rebuild Visual Studio project:
```cmd
cd C:\Users\waldo\Documents\GitHub\MyPC\GameBoySimulator\verilator
"C:\Program Files\Microsoft Visual Studio\2022\Community\MSBuild\Current\Bin\MSBuild.exe" sim.vcxproj /p:Configuration=Release /p:Platform=x64 /t:Rebuild
```

Run GUI and check DMG DEBUG window to confirm `lcd_data_gb = 0` (stuck).

### Step 2: Investigate VRAM Write Blocking

Check GameBoy core RTL for VRAM write control:
1. Is there a VRAM write enable signal?
2. Is it controlled by LCDC register?
3. Is it controlled by LCD mode?
4. Are boot ROM writes reaching VRAM module?

Possible issues:
- LCDC register not disabling LCD properly
- VRAM write enable stuck at 0
- Address decode not routing $8000-$9FFF to VRAM
- VRAM module not accepting writes
- Timing issue between CPU write and VRAM latching

### Step 3: Workaround - Force VRAM Pattern

For testing, you could modify the VRAM module to initialize with a pattern:

```verilog
// In VRAM module initialization
initial begin
    // Force a test pattern
    vram[0] = 8'hFF;  // Black stripe
    vram[1] = 8'hFF;
    vram[2] = 8'h00;  // White stripe
    vram[3] = 8'h00;
    vram[4] = 8'hAA;  // Gray stripe
    vram[5] = 8'hAA;
    // ...
end
```

If this shows a pattern on screen, it confirms:
- ✅ LCD controller can read VRAM correctly
- ✅ DMG conversion works
- ❌ Only VRAM writes are broken

---

## Summary Table

| Component | Status | Evidence |
|-----------|--------|----------|
| CPU Execution | ✅ Working | 212K ce_cpu pulses |
| Boot ROM Download | ✅ Working | Fixed in test, already correct in GUI |
| LCD Controller | ✅ Active | 3 frames rendered, modes cycling |
| DMG Conversion | ✅ **WORKING** | 0 → 255 (white) in test |
| isGBC_game | ✅ Correct | 0 (DMG mode) |
| **VRAM Writes** | ❌ **BROKEN** | Only 1 access detected |
| **lcd_data_gb** | ❌ **Stuck at 0** | Never varies across 3.4M cycles |
| **Final Output** | ❌ Wrong | Solid color (white/black) instead of graphics |

---

## Files Created

- `test_lcd_diagnostics.cpp` - Comprehensive LCD monitoring (DONE)
- `test_vram_writes.cpp` - VRAM write detection (DONE)
- `LCD_BLACK_SCREEN_ROOT_CAUSE.md` - Detailed analysis (DONE)
- `FINAL_DIAGNOSIS_SUMMARY.md` - This file (DONE)

---

## Confidence Level

**✅ 100% Confident:** DMG conversion logic is correct and working
**✅ 100% Confident:** lcd_data_gb is stuck at 0
**✅ 95% Confident:** VRAM is not initialized (writes blocked/not persisting)
**⚠️ 50% Confident:** Why GUI shows black instead of white (need more data)

**Recommendation:** Focus on VRAM write enable logic in GameBoy core RTL.
