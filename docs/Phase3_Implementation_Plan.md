# Phase 3: Algorithm Accuracy Implementation Plan

**Date:** 2025-11-14
**Status:** In Progress
**Goal:** Achieve accurate range reduction results

---

## Algorithm Analysis

### Current Problem

The Phase 2 algorithm has fundamental flaws:

```verilog
// Current (WRONG):
1. Extract mantissa only (64 bits)
2. Multiply mantissa * 2/π[chunk0]
3. Extract quadrant and fraction
4. Multiply fraction * π/2
```

**Why it fails:**
- Mantissa alone doesn't represent the angle value
- Missing the exponent means we lose magnitude information
- Example: Angle 1000π has exponent 0x400A, mantissa 0x8000000054A01800
  - Just using mantissa ≈ 1.00000003 × 2^63 (wrong scale)
  - Actual value needs: mantissa × 2^(exponent - bias - 63)

### Correct Approach

**Payne-Hanek requires:**
1. Convert FP80 angle to scaled integer representation
2. Select appropriate bits of 2/π based on exponent
3. Multi-precision multiplication
4. Extract integer (quadrant) and fraction
5. Convert fraction back to FP80 in range [0, 1)
6. Multiply by π/2

**Simplified but correct algorithm for Phase 3:**

Since we have limited microcode complexity, we'll use a pragmatic approach:

```
Input: angle (FP80) = sign × 2^(exp-bias) × mantissa

Step 1: Use FPU to compute angle * (2/π)
  - This gives us n = angle × 0.636619...
  - Load 2/π as FP80 constant (not raw bits)
  - Use FPU multiply directly

Step 2: Extract integer and fractional parts
  - Integer part = floor(n) → quadrant = int_part mod 4
  - Fractional part = n - int_part

Step 3: Multiply fractional part by π/2
  - Result is reduced angle in [0, π/2)

Step 4: Return reduced angle and quadrant
```

**Advantages:**
- Uses FPU arithmetic (accurate, handles exponents)
- Much simpler microcode
- Leverages existing hardware properly

**Trade-off:**
- Loses some precision for very large angles (> 2^63)
- But adequate for practical range (< 10^10)

---

## Phase 3 Implementation Strategy

### Option A: Use FPU Arithmetic (RECOMMENDED)

**Algorithm:**
```
1. Load 2/π as FP80 constant
2. angle_scaled = angle × (2/π)    [FPU multiply]
3. int_part = floor(angle_scaled)  [FPU round down]
4. frac = angle_scaled - int_part  [FPU subtract]
5. quadrant = int_part mod 4       [Extract low 2 bits]
6. reduced = frac × (π/2)          [FPU multiply]
7. Return reduced angle and quadrant
```

**Microcode ops needed:**
- Existing: MOP_CALL_ARITH (multiply, subtract)
- New: MOP_FLOOR (round down to integer)
- New: MOP_MOD4 (extract bits 1:0)

**Advantages:**
- Correct handling of exponents
- Uses proven FPU arithmetic
- Much simpler than multi-precision

**Estimated effort:** 4-6 hours
**Accuracy:** Excellent for angles < 2^52

### Option B: True Multi-Precision Payne-Hanek

Keep the current approach but fix it:
1. Properly scale mantissa by exponent
2. Use multiple chunks of 2/π
3. Correct bit alignment

**Estimated effort:** 12-16 hours
**Accuracy:** Excellent for all angles

### Decision: Go with Option A

Option A is the right choice because:
- Much simpler and faster to implement
- Leverages existing FPU correctly
- Adequate accuracy for practical use
- Aligns with hybrid design philosophy

---

## Implementation Tasks

### Task 1: Add 2/π as FP80 Constant to ROM ✓

Already have it at ROM address (calculate): 2/π = 0.6366197723675814...

FP80 representation:
- Sign: 0
- Exponent: 0x3FFE (bias=16383, exponent=-1, so 2^-1 = 0.5 range)
- Mantissa: 0xA2F9836E4E441529 (with implicit bit set)

Actually, let me compute this correctly:
2/π = 0.63661977236758134...
= 1.27323954473516268... × 2^(-1)

In FP80:
- Sign: 0
- Exponent: 0x3FFE (represents 2^(-1))
- Mantissa (with integer bit): 0xA2F9836E4E441529

Let me add this as ROM address 5.

### Task 2: Implement MOP_FLOOR

Extract integer part of FP80 number:
- If exp < 0x3FFF: return 0 (value < 1.0)
- If exp >= 0x3FFF + 64: return value as-is (already integer)
- Otherwise: Shift mantissa right by (63 - (exp - 0x3FFF)) bits

### Task 3: Revise Microcode Routine

New microcode at 0x0180:
```
0x0180: LOAD_A              // Load input angle
0x0181: LOAD_ROM 5          // Load 2/π as FP80
0x0182: LOAD_ROM_DATA       // Wait cycle, get 2/π into temp
0x0183: MOVE_ROM_TO_B       // 2/π into operand B
0x0184: CALL_ARITH 2        // angle × (2/π)
0x0185: WAIT_ARITH
0x0186: LOAD_ARITH_RES      // n = angle × (2/π)
0x0187: MOVE_RES_TO_C       // Save n
0x0188: FLOOR               // floor(n) → int_part
0x0189: MOVE_RES_TO_A       // int_part
0x018A: MOD4                // quadrant = int_part mod 4
0x018B: MOVE_RES_TO_D       // Save quadrant
0x018C: MOVE_C_TO_A         // Restore n
0x018D: MOVE_FLOOR_TO_B     // int_part to B
0x018E: CALL_ARITH 1        // n - int_part (subtract)
0x018F: WAIT_ARITH
0x0190: LOAD_ARITH_RES      // frac = n - int_part
0x0191: LOAD_ROM 4          // Load π/2
0x0192: LOAD_ROM_DATA
0x0193: MOVE_ROM_TO_B
0x0194: MOVE_RES_TO_A       // frac to A
0x0195: CALL_ARITH 2        // frac × (π/2)
0x0196: WAIT_ARITH
0x0197: LOAD_ARITH_RES      // reduced angle
0x0198: MOVE_QUADRANT_TO_B  // Restore quadrant
0x0199: RET
```

This is about 26 instructions (vs 18 before), but much more correct.

### Task 4: Add New Micro-Operations

Need to add:
- MOP_FLOOR: Floor operation on FP80
- MOP_MOD4: Extract bits 1:0 for quadrant
- Helper moves for multi-register juggling

---

## Simplified Implementation for Phase 3

Actually, let me think about this more carefully. The mock arithmetic unit in the testbench is very simplified. For Phase 3, I should:

**Pragmatic Phase 3 Approach:**

1. Keep the microcode structure similar
2. Fix the key bug: Use the full FP80 angle, not just mantissa
3. Use FPU multiply for angle × (2/π)
4. Implement simple integer/fraction extraction
5. Verify results are reasonable

Let me implement a working version that's between "too simple" and "too complex".

---

## Revised Phase 3 Plan (Executable)

### Step 1: Add 2/π FP80 Constant to ROM

Address 5: 2/π = 0x3FFE_A2F9836E4E441529

### Step 2: Revise Microcode (Simplified Correct Version)

```
1. Load angle (full FP80, not just mantissa)
2. Multiply angle by 2/π (FPU multiply, handles exponent)
3. Result is in units of π/2 (scaled angle)
4. Extract integer part for quadrant
5. Extract fractional part
6. Multiply fractional part by π/2
7. Return reduced angle
```

### Step 3: Implement MOP_FRAC for Fractional Part

Extract fractional part of FP80:
- If value < 1.0: return value
- Otherwise: return value - floor(value)

### Step 4: Test and Validate

Run tests with new algorithm, expect much better accuracy.

Let me start implementing this now.
