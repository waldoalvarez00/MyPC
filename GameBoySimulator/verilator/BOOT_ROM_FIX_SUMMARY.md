# Boot ROM Disable Fix - Critical Bug Resolved

**Date:** December 9, 2025
**Status:** ✅ **FIXED**

---

## Problem Summary

The GameBoy simulator displayed a black screen on Windows (and white screen on Linux) because the boot ROM never completed execution and never disabled itself.

---

## Root Cause

**File:** `gameboy_core/rtl/gb.v:914`

**Incorrect Code:**
```verilog
if((cpu_addr == 16'hff50) && !cpu_wr_n_edge && cpu_do[0]) begin
    boot_rom_enabled <= 1'b0;
end
```

**Problem:** The logic checked for `cpu_do[0]` (bit 0 must be 1), but the DMG boot ROM writes `$40` (0b01000000) to $FF50, which has **bit 0 = 0**.

---

## Investigation Steps

1. **Initial Black Screen Report:** User reported black screen on Windows, lcd_data showing constant value 3 (black)

2. **Boot ROM Execution Test:** Created `test_cpu_execution.cpp` which revealed:
   - Boot ROM executes correctly
   - 446 VRAM writes detected
   - Boot ROM **never disables** (stays enabled for all cycles)

3. **$FF50 Write Detection:** Created `test_ff50_write.cpp` which showed:
   - CPU **DOES write to $FF50** at cycle 4,188,536
   - Boot ROM stays enabled despite the write
   - 81 total accesses to $FF50 (mostly reads)

4. **Data Value Check:** Created `test_ff50_data.cpp` with new debug signal `dbg_cpu_do`:
   - Boot ROM writes `$40` to $FF50
   - Bit 0 = 0 (condition fails!)

5. **Documentation Research:** Confirmed via [Pan Docs](https://gbdev.io/pandocs/Power_Up_Sequence.html) and [Gbdev Wiki](https://gbdev.gg8.se/wiki/articles/Gameboy_Bootstrap_ROM):
   - **ANY write to $FF50 disables the boot ROM**
   - Not just writes with specific bit patterns

---

## The Fix

**File:** `gameboy_core/rtl/gb.v:914-916`

**Corrected Code:**
```verilog
// ANY write to $FF50 disables boot ROM (not just bit 0 set)
if((cpu_addr == 16'hff50) && !cpu_wr_n_edge) begin
    boot_rom_enabled <= 1'b0;
end
```

**Change:** Removed the incorrect `cpu_do[0]` check.

---

## Verification

**Test:** `test_ff50_data.cpp`

**Before Fix:**
```
Cycle 4188537: WRITE to $FF50 = $40 (bit 0 = 0)
  boot_enabled before: 1
  boot_enabled after +10: 1     ← STAYS ENABLED
```

**After Fix:**
```
Cycle 4188538: WRITE to $FF50 = $40 (bit 0 = 0)
  boot_enabled before: 1
  boot_enabled after +5: 0      ← ✅ DISABLED!
  boot_enabled after +10: 0
```

---

## Additional Changes

**File:** `gameboy_sim.v`

Added debug output for CPU data bus:
```verilog
output [7:0] dbg_cpu_do /*verilator public_flat*/;
...
assign dbg_cpu_do = gameboy.cpu_do;
```

This allows test programs to monitor what data is being written to I/O registers.

---

## Impact

- ✅ Boot ROM now completes execution correctly
- ✅ Boot ROM disables at the proper time
- ✅ Control transfers to cartridge at $0100
- ✅ Display should now show boot logo and cartridge graphics

---

## Next Steps

1. Rebuild Windows Visual Studio project with fix
2. Test GUI simulator to verify display works
3. Confirm Nintendo logo appears during boot sequence
4. Verify cartridge games run properly

---

## References

- [Pan Docs - Power-Up Sequence](https://gbdev.io/pandocs/Power_Up_Sequence.html)
- [Gbdev Wiki - Gameboy Bootstrap ROM](https://gbdev.gg8.se/wiki/articles/Gameboy_Bootstrap_ROM)
- [Game Boy boot ROM disassembly](https://gist.github.com/knightsc/ab5ebda52045b87fa1772f5824717ddf)

---

## Files Modified

1. `gameboy_core/rtl/gb.v` - Fixed boot ROM disable logic (line 914-916)
2. `gameboy_sim.v` - Added `dbg_cpu_do` debug output (lines 87, 521)

## Test Files Created

1. `test_ff50_write.cpp` - Monitors for $FF50 writes
2. `test_ff50_data.cpp` - Shows data value written to $FF50
3. `test_isgbc_status.cpp` - Checks GBC mode status
4. `test_cpu_execution.cpp` - Monitors CPU execution and boot ROM state
5. `test_cpu_long.cpp` - Extended 10M cycle test

---

**Status:** Ready for Windows Visual Studio rebuild and testing
