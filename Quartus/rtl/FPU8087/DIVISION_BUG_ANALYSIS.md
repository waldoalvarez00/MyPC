# FPU_IEEE754_Divide Critical Bug Analysis

## Bug Summary
**Status**: CRITICAL - Blocks SQRT microcode implementation
**Location**: FPU_IEEE754_Divide.v
**Impact**: Division returns zero when dividend mantissa < divisor mantissa

## Problem Description

The division unit uses a restoring division algorithm that FAILS when `mant_a < mant_b`:

```
16.0 / 8.5:
- mant_a = 0x8000000000000000 (16.0)
- mant_b = 0x8800000000000000 (8.5)
- Result: 0x00000000... (WRONG! Should be ~1.882)
```

## Root Cause Analysis

### Algorithm Overview
```verilog
dividend = {mant_a, 64'd0};  // 128-bit dividend
for (i = 0; i < 67; i++) {
    if (dividend[127:64] >= divisor) {
        dividend[127:64] -= divisor;
        quotient[66-i] = 1;
    }
    dividend <<= 1;
}
```

### Why It Fails

**Iteration 0:**
- dividend[127:64] = 0x8000000000000000
- divisor = 0x8800000000000000
- Compare: 0x8000... < 0x8800... → MISS
- NO subtraction, quotient[66] stays 0
- Shift dividend left

**After Shift:**
- {0x8000000000000000, 0x0000000000000000} << 1
- = {0x0000000000000001, 0x0000000000000000}
- dividend[127:64] now only 0x0000...0001 (MSB lost!)

**Iterations 1-66:**
- dividend[127:64] stays tiny (0x1, 0x2, 0x4, ...)
- ALL comparisons fail (too small vs 0x8800...)
- quotient remains 0x00000000...

### Mathematical Issue

The algorithm requires **131 bits of precision** (64-bit mantissa + 67-bit quotient), but only has **128 bits** available in the dividend register.

When `mant_a < mant_b`, the first iteration fails, and the MSB shifts out, leaving insufficient precision for subsequent iterations.

## Attempted Fixes

### Fix 1: Replicate Mantissa `{mant_a, mant_a}`
**Result**: FAILED
**Reason**: Both halves have MSB set, so after one shift both MSBs are lost.

```
{0x8000..., 0x8000...} << 1 = {0x0000...0001, 0x0000...0000}
```

### Fix 2: Extended Precision `{mant_a, mant_a >> 1}`
**Result**: FAILED
**Reason**: After shift, still only 1 bit in upper half.

### Fix 3: Pre-shift Dividend
**Result**: FAILED
**Reason**: Can't shift a 64-bit value with MSB=1 left without losing the MSB in a 64-bit container.

### Fix 4: Increase Iterations to 128
**Result**: WON'T WORK
**Reason**: Even with infinite iterations, 0x8000... < 0x8800... always fails.

## Correct Solutions

### Option A: SRT Division (Recommended)
- Sweeney-Robertson-Tocher algorithm
- Handles quotient digits {-2, -1, 0, 1, 2}
- More complex but robust
- Used in real hardware (Intel, AMD)

### Option B: Non-Restoring Division
- Simpler than SRT
- Allows negative remainders
- Requires quotient correction at end

### Option C: Goldschmidt Division
- Multiplicative convergence
- Different algorithm entirely
- May be simpler for FPGA

### Option D: Digit-by-Digit SQRT
- Avoid division entirely for SQRT
- Implement sqrt directly with digit extraction
- More cycles but avoids division dependency

## Impact on SQRT Microcode

Newton-Raphson SQRT requires: `x_{n+1} = 0.5 × (x_n + S/x_n)`

When `S < x_n`, the division `S / x_n` triggers this bug.

**Example**: sqrt(16.0)
- Iteration 1: x_0 = 16.0
- Compute: 16.0 / 16.0 → Works (equal mantissas)
- Result: x_1 = 8.5

- Iteration 2: x_1 = 8.5
- Compute: 16.0 / 8.5 → **BUG!** (0x8000... < 0x8800...)
- Returns 0 instead of 1.882
- SQRT fails completely

## Test Coverage

### Current Tests
- ✓ 12.0 / 3.0 (equal mantissas) - PASSES
- ✗ 16.0 / 8.5 (mant_a < mant_b) - NOT TESTED until SQRT

### Required Tests
- Division with mant_a < mant_b
- Division with various mantissa ratios
- Edge cases (0.5 ≤ quotient < 1.0)

## Recommendations

1. **Immediate**: Implement SRT or Non-Restoring division algorithm
2. **Testing**: Add comprehensive division test suite
3. **Alternative**: For SQRT only, use digit-by-digit algorithm
4. **Long-term**: Review all FPU arithmetic units for similar precision issues

## Files Affected
- `FPU_IEEE754_Divide.v` - Requires algorithm rewrite
- `MicroSequencer_Extended.v` - SQRT microcode blocked
- `tb_hybrid_execution.v` - Need mant_a < mant_b test cases

## References
- Intel 8087 used SRT division
- IEEE 754-2008 doesn't mandate algorithm, only precision
- Goldschmidt: "Division by convergence" (IBM)
- SRT: Sweeny (1965), Robertson (1958), Tocher (1956)

---
**Analysis Date**: 2025-11-09
**Commit**: WIP (division bug documented, not yet fixed)
