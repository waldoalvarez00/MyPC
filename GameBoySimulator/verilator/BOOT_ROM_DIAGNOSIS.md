# GameBoy Boot ROM White Screen Diagnosis - COMPLETE

## Problem
Display stays white despite LCD being enabled (LCDC=$91, lcd_on=1).

## Root Cause Analysis

### Investigation Steps

1. **LCDC Register Check** ✅ FIXED
   - Boot ROM writes $91 to $FF40 at cycle 11275
   - LCD turns on successfully
   - Status: Working correctly after video_sim.v fix

2. **VRAM Write Count** ⚠️ ISSUE FOUND
   - Expected: 96+ bytes (48 tiles × 2 bytes for Nintendo logo)
   - Actual: Only 7 VRAM writes total
   - This explains white screen - no logo data in VRAM

3. **Logo Copy Loop Analysis** ⚠️ LOOP NOT EXECUTING
   - Loop at $0006-$000B should copy logo from ROM to VRAM
   - Loop iterations: 0 (should be ~48)
   - Loop enters once and exits immediately

4. **HL Register Investigation** ⚠️ ROOT CAUSE
   - HL should be loaded with $0104 (Nintendo logo address in cart ROM)
   - Actual HL value when loop starts: $0000
   - This means loop terminates immediately (BIT 5, H is already set when H=$00)

5. **Boot ROM Execution Before Loop** 🔴 **CRITICAL BUG**
   - PC=$0004-$0005: Executing "LD HL, nn" instruction (opcode $21)
   - Spends 128 cycles stuck at this instruction
   - HL remains $0000 throughout
   - **Conclusion: The cart ROM read is returning $0000 instead of the logo address**

## Root Cause

**Cart ROM is not providing valid data during boot ROM execution.**

The boot ROM instruction at $0004 is:
```
$0004: 21 04 01    LD HL, $0104    ; Load address of Nintendo logo
```

The CPU correctly fetches opcode $21 (LD HL, nn), but when it tries to read the
16-bit immediate operand from $0005-$0006, it gets $0000 instead of $0104.

This causes HL to be loaded with $0000 instead of $0104, which means:
1. The logo copy loop at $0006 checks "BIT 5, H"
2. With H=$00, bit 5 is already 0, so Z flag is set
3. "JR Z, -5" doesn't jump (Z should cause jump, but our previous fix inverted this)
4. Loop exits immediately without copying logo data

## Why Cart ROM Returns Zeros

The boot ROM execution reads from boot ROM addresses $0000-$00FF, but for the
"LD HL, nn" instruction, the CPU needs to fetch the immediate operand bytes.
These bytes are part of the boot ROM binary itself.

**Hypothesis**: The cart ROM / external bus is being selected instead of boot ROM
for the immediate operand fetch, and the cart ROM at those addresses contains zeros.

## Next Steps

1. Verify boot ROM data at $0004-$0006:
   - Should be: 21 04 01
   - Check if boot ROM is properly loaded

2. Check boot ROM address decoding:
   - Is boot ROM selected for ALL addresses $0000-$00FF?
   - Are instruction fetches and data fetches both using boot ROM?

3. Check cart ROM initialization:
   - The test only writes one word to cart at $0100
   - Rest of cart ROM may be uninitialized (zeros)

## Test Results Summary

```
=== Logo Copy Loop Execution ===
Loop iterations: 0
VRAM writes: 7
First write: $8000 (from loop doing one copy with HL=$8000)
Subsequent writes: At different PC addresses (not from logo loop)

=== HL Register Initialization ===
PC=$0004-$0005: LD HL, nn instruction
Cycles spent: 128
HL value after: $0000
Expected HL: $0104
Status: FAILED - reads $0000 instead of $0104

=== Boot ROM Bytes ===
$0004: 21 (LD HL, nn opcode) ✓
$0005: ?? (should be $04 - LOW byte of address)
$0006: ?? (should be $01 - HIGH byte of address)
```

## Files Affected

- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/test_logo_copy_loop.cpp`
- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/test_loop_detail.cpp`
- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/test_before_loop.cpp`

## Status

✅ Diagnosis Complete
🔧 Ready for Fix: Boot ROM data fetch or address decoding issue
