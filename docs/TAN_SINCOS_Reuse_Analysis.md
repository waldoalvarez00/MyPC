# Analysis: Reusing SINCOS for TAN with Microcode Orchestration

**Date:** 2025-11-11
**Question:** Can we reuse the SINCOS unit with division for TAN to save area, possibly with microcode orchestration?

---

## Quick Answer

**Current Implementation Already Does This!** ✅

The existing FPU_Transcendental.v implementation **already reuses** the CORDIC engine and division for TAN:

1. **FPTAN:** CORDIC rotation → sin/cos → **divide sin/cos** using shared unit → return tan
2. **FSINCOS:** CORDIC rotation → sin/cos → return both

**Additional area savings from microcode orchestration: ~200-500 gates (negligible)**

---

## Current Implementation Analysis

### How FPTAN Currently Works (FPU_Transcendental.v)

**Step 1: Route to CORDIC (lines 327-333)**
```verilog
OP_TAN: begin
    // Tangent: compute sin/cos, then need to divide
    // For now, just compute sin and cos
    cordic_enable <= 1'b1;
    cordic_mode <= 1'b0;  // Rotation mode
    state <= STATE_WAIT_CORDIC;
end
```

**Step 2: After CORDIC completes, divide (lines 400-410)**
```verilog
OP_TAN: begin
    // Have sin and cos, now divide: tan = sin/cos using shared MulDiv unit
    ext_muldiv_req <= 1'b1;
    ext_muldiv_op <= 1'b1;  // 1 = divide
    ext_muldiv_a <= cordic_sin_out;  // sin(θ)
    ext_muldiv_b <= cordic_cos_out;  // cos(θ)
    // Note: Also push 1.0 per Intel spec (for compatibility)
    result_secondary <= FP80_ONE;
    has_secondary <= 1'b1;
    state <= STATE_WAIT_DIV;
end
```

**Step 3: Return result**
```verilog
STATE_WAIT_DIV: begin
    ext_muldiv_req <= 1'b0;
    if (ext_muldiv_done) begin
        result_primary <= ext_muldiv_result;
        state <= STATE_DONE;
    end
end
```

### Comparison: FPTAN vs FSINCOS

| Operation | CORDIC Call | Post-Processing | Results Returned |
|-----------|-------------|-----------------|------------------|
| **FSINCOS** | Rotation mode | None | sin(θ), cos(θ) |
| **FPTAN** | Rotation mode | **Divide sin/cos** | tan(θ), 1.0 |
| **FSIN** | Rotation mode | None | sin(θ) |
| **FCOS** | Rotation mode | None | cos(θ) |

**Key Observation:** All operations use the **same CORDIC engine**. The only difference is post-processing.

---

## What's Already Shared

### Hardware Already Shared (via Strategy 1)

1. **CORDIC Engine** (~12,000 gates)
   - Used by: FSIN, FCOS, FSINCOS, FPTAN, FPATAN
   - ✅ Already shared, cannot share more

2. **Division Unit** (~15,000 gates)
   - Used by: FDIV, FPTAN (via ext_muldiv_req)
   - ✅ Already shared via Strategy 1

3. **Multiply Unit** (~12,000 gates)
   - Used by: FMUL, FYL2X, FYL2XP1
   - ✅ Already shared via Strategy 1

4. **AddSub Unit** (~8,000 gates)
   - Used by: FADD, FSUB, FYL2XP1
   - ✅ Already shared via Strategy 1 + 2D

**Conclusion:** The big ticket items are already shared!

---

## What Could Microcode Save?

### Hardware-Only Approach (Current)

**OP_TAN State Machine Logic:**
```verilog
// In STATE_ROUTE_OP:
OP_TAN: begin
    cordic_enable <= 1'b1;
    cordic_mode <= 1'b0;
    state <= STATE_WAIT_CORDIC;
end  // ~50 gates

// In STATE_WAIT_CORDIC:
OP_TAN: begin
    ext_muldiv_req <= 1'b1;
    ext_muldiv_op <= 1'b1;
    ext_muldiv_a <= cordic_sin_out;
    ext_muldiv_b <= cordic_cos_out;
    result_secondary <= FP80_ONE;
    has_secondary <= 1'b1;
    state <= STATE_WAIT_DIV;
end  // ~150 gates

// STATE_WAIT_DIV handling (shared with other ops): ~100 gates
```

**Total OP_TAN-specific logic: ~300 gates**

### Microcode Approach

**Microcode Sequence:**
```
TAN_microcode:
    CALL FSINCOS           ; Get sin(θ) and cos(θ)
    ; Stack now has: cos(θ) on top, sin(θ) below
    SWAP                   ; Swap to get sin on top
    FDIV                   ; Divide sin/cos
    PUSH_CONST 1.0         ; Push 1.0 for compatibility
    RET
```

**Hardware Removed:**
- OP_TAN case in STATE_ROUTE_OP: ~50 gates
- OP_TAN case in STATE_WAIT_CORDIC: ~150 gates
- Some STATE_WAIT_DIV handling: ~50 gates
- **Total: ~250 gates saved**

**Hardware Added:**
- Microcode ROM entry (6 instructions): ~48 bytes
- Microcode sequencer overhead: +100 gates
- **Total: +100 gates added**

**Net Savings: ~150-200 gates (0.04% of FPU)**

---

## Performance Impact

### Current Hardware Implementation

| Operation | Cycles | Notes |
|-----------|--------|-------|
| FPTAN | ~60 cycles | 50 CORDIC + 10 divide |
| FSINCOS | ~50 cycles | 50 CORDIC only |

### Microcode Implementation

| Operation | Cycles | Notes |
|-----------|--------|-------|
| FPTAN (microcode) | ~85-95 cycles | FSINCOS(50) + SWAP(2) + FDIV(35) + overhead(5) |

**Performance Penalty: +40-50% for FPTAN**

### Impact on Overall Performance

Assuming FPTAN is 2% of all FPU operations:
- **Weighted impact: 0.02 × 50% = 1% total system slowdown**

---

## Alternative Approaches Analyzed

### Approach 1: Remove OP_TAN, Use Microcode

**Pros:**
- Saves ~150-200 gates
- Simplifies hardware state machine slightly

**Cons:**
- FPTAN becomes 40-50% slower
- Adds microcode complexity
- Minimal area savings (0.04% of FPU)

**Verdict:** ❌ **NOT RECOMMENDED** - Poor cost/benefit ratio

---

### Approach 2: Make FPTAN Call FSINCOS Internally

**Idea:** Have OP_TAN internally call OP_SINCOS logic, then divide the results.

**Current Implementation:**
```
OP_TAN → CORDIC → divide sin/cos
```

**Proposed Implementation:**
```
OP_TAN → (call OP_SINCOS logic) → divide results
```

**Analysis:**
- This is **already essentially what happens**
- CORDIC is called the same way for both operations
- Only difference is post-processing
- **No area savings** because CORDIC is already shared

**Verdict:** ❌ **ALREADY DONE** - Current implementation already does this

---

### Approach 3: Move ALL Transcendental to Microcode (Strategy 2C)

This was analyzed in `FPU_Microcode_Migration_Analysis.md`:

**Area Savings:** ~39,000 gates (11.3% of FPU)
- CORDIC logic: 12,000 gates
- Polynomial evaluator: 22,000 gates (now done via Strategy 2D)
- Range reduction: 5,000 gates

**Performance Penalty:** ~25% average
- FSIN/FCOS: ~55 → ~180 cycles (+227%)
- FPTAN: ~60 → ~200 cycles (+233%)

**Verdict:** ❌ **NOT RECOMMENDED** - Too much performance degradation

---

## Detailed Area Breakdown

### Current TAN Implementation

| Component | Area | Sharing Status |
|-----------|------|----------------|
| CORDIC engine | 12,000 gates | ✅ Shared with FSIN/FCOS/FPATAN |
| Range reduction | 5,000 gates | ✅ Shared with all trig ops |
| Atan table | 5,000 gates | ✅ Shared with all CORDIC ops |
| Division unit | 15,000 gates | ✅ Shared via Strategy 1 |
| **OP_TAN state logic** | **~300 gates** | ❌ TAN-specific |
| **Total TAN-specific** | **~300 gates** | **Only this is removable** |

### If Moved to Microcode

| Component | Change |
|-----------|--------|
| OP_TAN state logic | -300 gates |
| Microcode ROM entry | +100 gates |
| **Net Savings** | **~200 gates** |
| **Percentage of FPU** | **0.06%** |

---

## Why So Little to Save?

### The Key Insight: Hardware is Already Optimally Shared

1. **CORDIC Engine** - Shared by 5 operations (FSIN, FCOS, FSINCOS, FPTAN, FPATAN)
2. **Division** - Shared via Strategy 1 (ext_muldiv_req interface)
3. **Multiplication** - Shared via Strategy 1 (ext_muldiv_req interface)
4. **AddSub** - Shared via Strategy 1 + 2D (ext_addsub_req interface)

**The expensive hardware is already maximally shared!**

### What's Not Shared: Control Logic

The **only** TAN-specific logic is:
- Case statement handling (~50 gates)
- Result routing (~150 gates)
- State transition logic (~100 gates)

This is **lightweight control logic**, not expensive arithmetic hardware.

---

## Recommendation

### Primary Recommendation: Keep Current Implementation ✅

**Why:**
1. **Minimal Area Savings:** Only ~200 gates (0.06% of FPU)
2. **Significant Performance Penalty:** +40-50% slower for FPTAN
3. **Added Complexity:** Microcode development and testing overhead
4. **Already Optimized:** Hardware is already maximally shared

**Current Implementation Benefits:**
- ✅ CORDIC already shared across all trig operations
- ✅ Division already shared via Strategy 1
- ✅ Fast hardware execution (~60 cycles)
- ✅ Simple, proven implementation

### Alternative: Consider Only if Desperate for Area

If FPGA utilization exceeds 80% after synthesis:
- Moving TAN to microcode could save ~200 gates
- Accept 40-50% performance penalty for FPTAN
- But consider **Strategy 2A** (polynomial to microcode) first:
  - Saves 22,000 gates (110× more than TAN to microcode!)
  - Only affects F2XM1/FYL2X which are even rarer than FPTAN

---

## Comparison with Other Optimizations

| Optimization | Area Saved | Effort | Status |
|--------------|-----------|--------|--------|
| **Strategy 1** (Share trans units) | 33,000 gates | 4 hours | ✅ Done |
| **Strategy 2D** (Share poly units) | 20,000 gates | 4 hours | ✅ Done |
| **Strategy 2A** (Poly to microcode) | 22,000 gates | 5 weeks | Optional |
| **TAN to microcode** | **200 gates** | 1 week | ❌ Not worth it |

**ROI Analysis:**
- Strategy 1: 8,250 gates/hour
- Strategy 2D: 5,000 gates/hour
- Strategy 2A: 110 gates/hour
- **TAN to microcode: 5 gates/hour** ← Terrible ROI!

---

## Deeper Analysis: Why FPTAN is Already Optimal

### Mathematical Relationship

```
tan(θ) = sin(θ) / cos(θ)
```

**Two Implementation Approaches:**

**Approach A: Dedicated TAN Algorithm**
- Use CORDIC in circular mode with different iterations
- Directly compute tan without sin/cos intermediate
- **Area:** Same CORDIC hardware
- **Performance:** Slightly faster (~5 cycles)
- **Complexity:** More complex CORDIC control

**Approach B: Compute via Sin/Cos Division (Current)**
- Use standard CORDIC rotation for sin/cos
- Divide the results
- **Area:** Reuses existing CORDIC and division
- **Performance:** ~60 cycles (good enough)
- **Complexity:** Simple, proven approach

**Current implementation uses Approach B**, which is simpler and reuses more hardware.

### Intel 8087 Compatibility Note

The 8087 FPTAN instruction returns two values:
1. tan(θ) - the actual tangent
2. 1.0 - a constant (for backwards compatibility)

This is why `result_secondary <= FP80_ONE` and `has_secondary <= 1'b1` are set.

Microcode would need to handle this dual-result behavior, adding complexity.

---

## Conclusion

### Question: Can we save area by reusing SINCOS for TAN with microcode?

**Answer: The current hardware implementation ALREADY does this optimally!**

**What's Already Shared:**
- ✅ CORDIC engine (shared across all trig ops)
- ✅ Division unit (shared via Strategy 1)
- ✅ Control logic is minimal (~300 gates)

**Potential Microcode Savings:**
- ❌ Only ~200 gates (0.06% of FPU)
- ❌ Performance penalty: +40-50% for FPTAN
- ❌ Very poor ROI compared to other optimizations

**Recommendation:**
- ✅ **Keep current implementation** - it's already well-optimized
- ✅ Focus on higher-value optimizations (Strategy 2A if needed)
- ✅ Current strategies (1 + 2D) already saved 51,000 gates - plenty of headroom!

---

## Summary Table

| Approach | Area Saved | Performance | Complexity | Recommendation |
|----------|-----------|-------------|------------|----------------|
| **Current (hardware)** | Baseline | ~60 cycles | Simple | ✅ **KEEP** |
| Microcode TAN | +200 gates | ~95 cycles (+58%) | Medium | ❌ Not worth it |
| Internal SINCOS call | 0 gates | Same | Same | Already doing this |
| All trans to microcode | +39,000 gates | +227% | Very High | ❌ Too slow |

---

## Files Analyzed

- `Quartus/rtl/FPU8087/FPU_Transcendental.v` (lines 327-333, 400-410)
- `Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v`
- `FPU_Microcode_Migration_Analysis.md` (Strategy 2C analysis)
- `STRATEGY1_IMPLEMENTATION.md`
- `STRATEGY2D_IMPLEMENTATION.md`

---

*Analysis completed by Claude Code (Sonnet 4.5)*
*Session: claude/analyze-area-011CV1BWZv4GNP6sMW2rfsao*
