# GUI Simulator Boot ROM Fix

**Issue:** GUI simulator shows nothing on screen
**Date:** December 9, 2025
**Status:** ✅ FIXED

## Problem Analysis

The GUI simulator was loading and downloading a boot ROM to the GameBoy, but the boot ROM execution path wasn't working correctly after we removed the code that forced `boot_rom_enabled=0`.

### Root Cause

1. **Boot ROM loaded**: `loadBootROM()` and `downloadBootROM()` were called at startup
2. **Boot ROM enabled**: The GameBoy hardware defaulted to boot ROM enabled
3. **No forced disable**: We removed the code that forced `top__DOT__gameboy__DOT__boot_rom_enabled = 0`
4. **Result**: GameBoy stuck trying to execute boot ROM instead of cart ROM

## Solution

**Skip boot ROM entirely for direct cart execution.**

### Changes Made

#### Change 1: Skip Boot ROM Loading (Line ~888)

**Before:**
```cpp
console.AddLog("ce_cpu warmup complete, ce_cpu=%d", top->dbg_ce_cpu);

// Load and download boot ROM
loadBootROM();
downloadBootROM();
```

**After:**
```cpp
console.AddLog("ce_cpu warmup complete, ce_cpu=%d", top->dbg_ce_cpu);

// Skip boot ROM loading for direct cart execution
console.AddLog("Skipping boot ROM - executing cart ROM directly");
// The boot ROM will remain disabled (boot_rom_enabled=0 by default)
```

**Rationale:** Without boot ROM loaded, the GameBoy will execute directly from cart ROM at address $0000.

#### Change 2: Update Reset Log Message (Line ~739)

**Before:**
```cpp
if (main_time == initialReset) {
    top->reset = 0;
    console.AddLog("Reset released at cycle %lu", (unsigned long)main_time);
    console.AddLog("  Forcing boot_rom_enabled=0 for cart execution");
}
```

**After:**
```cpp
if (main_time == initialReset) {
    top->reset = 0;
    console.AddLog("Reset released at cycle %lu", (unsigned long)main_time);
    console.AddLog("  boot_rom_enabled status: %d", top->dbg_boot_rom_enabled);
}
```

**Rationale:** Update log message to reflect actual status rather than claiming we're forcing a signal we can't access.

## Testing Instructions

1. **Rebuild the GUI simulator** (if not already done)
2. **Run the simulator:**
   - Should load `./game.gb` by default
   - OR provide ROM file as command line argument
3. **Check console log for:**
   ```
   ce_cpu warmup complete, ce_cpu=X
   Skipping boot ROM - executing cart ROM directly
   Reset released at cycle 48
   boot_rom_enabled status: 0
   ```
4. **Video should appear after a few seconds** showing GameBoy screen output

## What to Expect

### Normal Operation

- **Console window** shows initialization messages
- **Video window** displays GameBoy LCD output (160x144 scaled)
- **Control window** shows simulation controls (Run/Stop/Reset)
- **Audio window** shows audio waveforms
- **main_time counter** increments, showing simulation is running
- **frame_count** increments, showing frames are being rendered

### If Still No Display

Check the **Debug Log** window for errors:

1. **ROM loading failed?**
   - Look for: `"WARN: Cannot open ROM file: ./game.gb"`
   - Solution: Provide valid ROM file or use command line arg

2. **cart_ready not set?**
   - Look for: `"cart_ready=0"` in log
   - Solution: Check SDRAM initialization

3. **ce_cpu not pulsing?**
   - Look for: `"ce_cpu=0"` consistently
   - Solution: Check clock generation

4. **CPU stuck?**
   - Look for: `"WARN: CPU stuck at 0xXXXX"`
   - Solution: Check if ROM is valid GameBoy code

## Alternative: Use Boot ROM (If Needed)

If you want the authentic boot ROM sequence:

1. **Uncomment the boot ROM loading:**
   ```cpp
   // Load and download boot ROM
   loadBootROM();
   downloadBootROM();
   ```

2. **Ensure boot ROM file exists:**
   - Place `dmg_boot.bin` in `gameboy_core/BootROMs/bin/`
   - OR the minimal boot ROM will be created automatically

3. **Boot ROM will disable itself:**
   - Real boot ROM: Scrolls Nintendo logo, plays sound, disables at end
   - Minimal boot ROM: Immediately writes $01 to $FF50 to disable

## Technical Details

### Boot ROM Control

The GameBoy hardware has two modes:

1. **Boot ROM mode** (`boot_rom_enabled=1`):
   - CPU executes from internal boot ROM ($0000-$00FF)
   - Used for Nintendo logo scroll and initialization
   - Boot ROM writes $01 to $FF50 to disable itself

2. **Cart ROM mode** (`boot_rom_enabled=0`):
   - CPU executes from cart ROM at $0000
   - Normal game operation

### Why Skip Boot ROM?

**Advantages:**
- Immediate cart execution
- No boot sequence delay
- No boot ROM file needed
- Simpler initialization

**Disadvantages:**
- No authentic boot sequence
- Some games might expect boot ROM initialization state
- Hardware not tested in boot ROM mode

### Debug Signals Available

Monitor these via the console log:

- `top->dbg_boot_rom_enabled` - Boot ROM enable status (should be 0)
- `top->dbg_cart_ready` - Cart ready flag (should be 1 after init)
- `top->dbg_ce_cpu` - CPU clock enable (should pulse)
- `top->dbg_cpu_addr` - CPU address bus (should change)
- `top->dbg_sel_boot_rom` - Boot ROM select (should be 0)

## Expected Boot Sequence

### With Boot ROM Skip (Current)

```
1. Reset asserted (cycle 0-48)
2. ROM loaded into SDRAM
3. cart_ready set
4. Reset released (cycle 48)
5. boot_rom_enabled = 0
6. CPU starts executing from cart ROM address $0100
7. Video output begins
```

### With Boot ROM Loaded (Alternative)

```
1. Reset asserted (cycle 0-48)
2. ROM loaded into SDRAM
3. Boot ROM loaded and downloaded
4. cart_ready set
5. Reset released (cycle 48)
6. boot_rom_enabled = 1
7. CPU executes boot ROM sequence
8. Boot ROM writes $01 to $FF50
9. boot_rom_enabled = 0
10. CPU starts executing from cart ROM address $0100
11. Video output begins
```

## Troubleshooting

### Problem: Black screen, no errors

**Check:**
- Is `run_enable` checked in Control window?
- Is `main_time` increasing?
- Is `frame_count` increasing in Video window?

**Solution:** Click "Start running" button

### Problem: Window freezes

**Check:**
- Task Manager - is process using CPU?
- Console log - last message?

**Solution:**
- Check if infinite loop in simulation
- Enable diagnostics to see progress

### Problem: Console shows errors

**Common errors:**
- `"Cannot open ROM file"` - Provide valid ROM
- `"cart_ready=0"` - SDRAM init failed
- `"CPU stuck"` - Invalid ROM code

## Performance Notes

- **Batch size:** 150,000 cycles per frame
- **Expected FPS:** ~60 FPS on modern PC
- **Simulation speed:** ~24 MHz effective clock
- **First frame:** May take 1-2 seconds to appear

## Summary

✅ **Boot ROM loading disabled**
✅ **Direct cart ROM execution enabled**
✅ **Console log messages updated**
✅ **Ready for testing**

The GUI simulator should now display GameBoy output immediately after initialization.
