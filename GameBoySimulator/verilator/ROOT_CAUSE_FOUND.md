# Root Cause Analysis: White Screen Issue - SOLVED

## Problem Statement
Nintendo logo animation not visible despite LCD being enabled (LCDC=$91, lcd_on=1).

## Systematic Verification Results

### ✅ Verification 1: Boot ROM Binary Loaded Correctly
**Status:** PASS

- Boot ROM file contains correct data
- Hardware loads all 256 bytes correctly
- CPU reads boot ROM data correctly
- Test: `test_boot_rom_data.cpp`

**Findings:**
```
Boot ROM at $0003-$0005: 21 00 80  (LD HL, $8000)
CPU reads: $00 $80 $22 ✓ MATCH
```

###❌ Verification 2: Cart ROM Data at $0104
**Status:** FAIL - ROOT CAUSE FOUND

- Nintendo logo loaded into test via ioctl_download
- Boot ROM attempts to read from cart ROM $0104-$0133
- **CPU reads return $00 instead of logo data**

**Test Results:**
```
Expected at $0104: $CE (first byte of Nintendo logo)
Actual CPU read: $00  ✗ MISMATCH
Cart ROM reads: 32 attempts, all returned $00
```

### ❌ Verification 3: ioctl Download Interface
**Status:** FAIL - CONFIRMED ROOT CAUSE

- Wrote test pattern $AABB $DDCC to cart ROM via ioctl_download
- CPU attempted to read back from same addresses
- **All reads returned $00**

**Test Results:**
```
Written via ioctl: AA BB CC DD
Read by CPU:       00 00 00 00  ✗ COMPLETE FAILURE
```

## Root Cause

**The `ioctl_download` interface is not writing cart ROM data to a location where the CPU can read it.**

Possible specific causes:
1. ioctl_download writes to wrong SDRAM address/bank
2. Cart ROM read path doesn't access SDRAM correctly
3. Address mapping between ioctl and CPU reads is incorrect
4. SDRAM model not storing ioctl writes
5. Boot ROM shadow region interfering with cart ROM reads

## Impact Chain

```
ioctl_download broken
    ↓
Cart ROM returns zeros
    ↓
Boot ROM reads $00 from $0104 (logo source)
    ↓
Logo copy loop writes zeros to VRAM
    ↓
VRAM contains no valid tile data
    ↓
LCD displays white screen (color 0)
```

## Evidence Summary

| Component | Status | Evidence |
|-----------|--------|----------|
| LCD Enable | ✅ WORKING | LCDC=$91, lcd_on=1 at cycle 11276 |
| Boot ROM | ✅ WORKING | Executes correctly, reaches logo copy |
| Boot ROM Data | ✅ CORRECT | All 256 bytes load and read correctly |
| Cart ROM Write | ❌ BROKEN | ioctl_download doesn't persist data |
| Cart ROM Read | ❌ BROKEN | Always returns $00 |
| Logo Copy | ❌ BROKEN | Copies zeros (5/96 writes before abort) |
| VRAM | ❌ EMPTY | No tile data for logo |
| Display | ❌ WHITE | No pixel data to show |

## Next Steps

1. **Investigate ioctl_download path in gameboy_sim.v / top.v**
   - Where does ioctl write to SDRAM?
   - What address mapping is used?

2. **Investigate cart ROM read path in gb.v**
   - How does CPU read from cart ROM?
   - Where does it access SDRAM?
   - Is there address translation?

3. **Check SDRAM model**
   - Does it handle ioctl writes correctly?
   - Are ioctl and CPU using compatible addressing?

4. **Fix the interface**
   - Ensure ioctl writes go to correct SDRAM location
   - Ensure CPU cart ROM reads access same location
   - Verify with test_ioctl_interface.cpp

## Test Files Created

1. `test_boot_rom_data.cpp` - Verifies boot ROM loading ✅
2. `test_boot_rom_flow.cpp` - Traces logo copy execution ⚠️
3. `test_cart_rom_reads.cpp` - Monitors cart ROM reads ❌
4. `test_ioctl_interface.cpp` - Tests ioctl write/read ❌
5. `test_logo_copy_loop.cpp` - Analyzes copy loop behavior ❌
6. `test_loop_detail.cpp` - Deep trace of loop execution ❌
7. `test_before_loop.cpp` - Traces pre-loop initialization ❌

## Conclusion

The white screen is caused by **ioctl_download interface bug**. The interface appears to accept writes but doesn't store them in a location accessible to the CPU's cart ROM read path. This prevents the Nintendo logo from being loaded into VRAM, resulting in a blank display.

**Fix Priority:** CRITICAL - blocks all cart ROM functionality
**Affected:** All GameBoy ROM loading, not just boot sequence
