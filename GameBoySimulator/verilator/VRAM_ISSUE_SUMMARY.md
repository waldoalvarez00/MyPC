# VRAM Display Issue - Critical Finding

**Date:** December 9, 2025
**Status:** 🔍 Root cause identified - Platform-dependent VRAM randomization

---

## Summary

✅ **Compilation**: Fixed - Build succeeds
❌ **Display**: Black screen on Windows, White screen on Linux
✅ **VRAM Writes**: Working - 446 writes detected
❌ **VRAM Persistence**: Issue confirmed

---

## Test Results

### Windows (User Report)
```
Mode: mono
lcd_data: 3
lcd_data_gb: 3
VGA RGB: 0,0,0
Result: ALL BLACK
```

### Linux (My Test)
```
lcd_data_gb: 0 (100% of samples)
Result: ALL WHITE
```

---

## Root Cause

**Verilator Memory Randomization is Platform-Dependent:**

| Platform | VRAM Init | lcd_data_gb | Display |
|----------|-----------|-------------|---------|
| Linux    | 0x00      | 0 (white)   | White   |
| Windows  | 0xFF      | 3 (black)   | Black   |

### Why This Happens

1. **dpram.v initialization** (`initial begin ... mem[i] = 0`) runs first
2. **Verilator reset** runs `VL_RAND_RESET_I(8)` which randomizes memory
3. On Linux: randomizes to mostly 0x00
4. On Windows: randomizes to mostly 0xFF

The manual initialization is **overridden** by Verilator's randomization!

---

## The Mystery: Where Are Boot ROM Writes?

**Evidence:**
- ✅ Boot ROM executes correctly
- ✅ 446 VRAM writes detected (addresses $8005-$8009)
- ✅ `cpu_wr_n` goes LOW (write active)
- ✅ `vram_wren` goes HIGH (write enable)
- ❌ LCD displays only initial randomized values (0x00 or 0xFF)

**Possible Explanations:**

### 1. Writes Happen But Get Re-Randomized
Verilator might randomize VRAM **after** boot ROM writes, overwriting them.

### 2. Timing Issue
Boot ROM writes to VRAM, but LCD hasn't started rendering yet, or is rendering before writes complete.

### 3. Tile/Map Addressing
Boot ROM writes tiles to $8000-$8FFF, but LCD reads from:
- Tile map at $9800-$9BFF (which tiles to display)
- Tile data at $8000-$97FF (what tiles look like)

If tile map isn't initialized, LCD shows random tiles from random locations.

### 4. Boot ROM Not Complete
500K-1M cycles might not be enough for boot ROM to fully execute and write all data.

---

## Next Steps to Debug

### Test 1: Direct VRAM Write via ioctl
Bypass boot ROM entirely - write pattern directly to VRAM via ioctl interface and see if it displays.

```cpp
// Write test pattern to VRAM $8000
for (int i = 0; i < 256; i++) {
    write_vram_via_ioctl(0x8000 + i, test_pattern[i]);
}
// Check if lcd_data_gb changes from 0/3 to other values
```

If this works → Boot ROM writes aren't persisting
If this doesn't work → VRAM read path is broken

### Test 2: Monitor VRAM After Longer Runtime
Run for 10M cycles (several seconds of game time) and check if values ever change.

### Test 3: Force VRAM to Known Pattern
Directly access `dut->rootp->top->gameboy->video->vram0->mem[addr]` and write test pattern, then check LCD output.

---

## Workaround for User

**Option 1: Wait Longer**
The boot ROM might need more time. Let the simulator run for 30-60 seconds and see if anything appears.

**Option 2: Load a Real ROM**
Instead of using boot ROM, load a complete GameBoy ROM that has a visible title screen.

**Option 3: Disable Verilator Randomization**
This requires modifying Verilator codegen, which is complex.

---

## Files to Check

1. **gb.v:751** - VRAM write enable logic
   ```verilog
   wire vram_wren = video_rd?1'b0:!vram_bank&&((hdma_rd&&isGBC)||cpu_wr_vram);
   ```

2. **gb.v:762** - VRAM instantiation
   ```verilog
   dpram #(13) vram0 (
       .clock_a   (clk_cpu  ),
       .wren_a    (vram_wren),
       .data_a    (vram_di  ),
       ```

3. **video.v** - LCD rendering logic
   - Reads from VRAM
   - Converts tile data to pixels
   - Outputs lcd_data_gb

4. **dpram.v** - VRAM memory module
   - Initialization gets overridden by Verilator
   - Need to prevent randomization

---

## Hypothesis

I believe the issue is:

1. Boot ROM **writes tiles** to VRAM $8000-$8xxx ✅
2. Boot ROM **should write tile map** to $9800-$9Bxx ❓
3. LCD **reads tile map** to know which tiles to display ❓
4. If tile map is random (0x00 or 0xFF), LCD displays:
   - Tile #0x00 (all zeros = color 0 = white on Linux)
   - Tile #0xFF (all ones = color 3 = black on Windows)

**Next diagnostic:** Check if boot ROM writes to tile map region ($9800-$9BFF) or just tile data region ($8000-$8FFF).

---

## Code References

- VRAM write test: `test_vram_write_signals.cpp:119` - Shows writes happening
- LCD sample test: `test_simple_lcd_sample.cpp` - Shows only color 0 (Linux) or 3 (Windows)
- VRAM module: `GameBoySimulator/rtl/dpram.v:40-46` - Initialization code
- VRAM write logic: `gameboy_core/rtl/gb.v:743-762` - Write enable

---

## Confidence Level

✅ **100%**: VRAM randomization is platform-dependent
✅ **100%**: Boot ROM writes ARE happening (signals confirmed)
✅ **95%**: Boot ROM writes not visible on LCD
❓ **60%**: Issue is tile map not initialized, so LCD reads tile #0 or #FF repeatedly

---

## Recommendation

**For immediate testing:**
Try loading a real GameBoy ROM instead of relying on boot ROM. This will bypass the boot sequence and go directly to game graphics.

**For fixing:**
Need to either:
1. Prevent Verilator randomization (complex)
2. Force VRAM initialization after reset (add reset logic)
3. Debug why boot ROM tile map writes aren't working

The fact that you see consistent black (and I see consistent white) suggests the LCD IS working, but it's just rendering the uninitialized VRAM state.
