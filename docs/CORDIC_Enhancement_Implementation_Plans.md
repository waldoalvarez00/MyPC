# CORDIC Enhancement Implementation Plans
**Date:** 2025-11-15
**Module:** FPU_CORDIC_Wrapper.v
**Objective:** Enhance CORDIC for 8087-accurate TAN/ATAN while preserving SIN/COS
**Design Constraint:** Keep SIN/COS untouched, make TAN/ATAN exactly match 8087

---

## Executive Summary

This document presents **5 implementation plans** for enhancing the CORDIC wrapper to match Intel 8087 behavior for TAN/ATAN operations while preserving the existing SIN/COS implementation. Each plan is evaluated on:

- **Hardware utilization** (ALM usage)
- **Unit reuse** (leveraging existing FPU modules)
- **Microcode integration** (CPU/FPU microsequencer usage)
- **Performance** (cycle counts)
- **Accuracy** (ULP error vs 8087)
- **Development effort** (engineering hours)

### Key Requirements

1. ✅ **Preserve SIN/COS:** Keep current 50-iteration CORDIC for rotation mode (no changes)
2. ✅ **Match 8087 TAN/ATAN:** Implement hybrid CORDIC (16 iterations) + rational/polynomial correction
3. ✅ **Proper FP80 Conversion:** Use format converter with rounding, denormal handling, exception flags
4. ✅ **Proper Quadrant Handling:** IEEE-compliant negate with special value handling
5. ✅ **Exception Handling:** Full 8087-compatible flags (Invalid, Overflow, Underflow, Inexact)

### Comparison Matrix

| Plan | Hardware (ALMs) | Unit Reuse | Microcode | Cycles (TAN) | Cycles (ATAN) | 8087 Match | Effort (hrs) |
|------|-----------------|------------|-----------|--------------|---------------|------------|--------------|
| **Plan 1: Full Hardware** | +285 | Medium | None | 35-40 | 35-40 | ✅ Exact | 40-50 |
| **Plan 2: Heavy Unit Reuse** | +120 | High | None | 50-70 | 50-70 | ✅ Exact | 30-40 |
| **Plan 3: Hybrid HW+Microcode** | +150 | High | Partial | 45-60 | 45-60 | ✅ Exact | 35-45 |
| **Plan 4: Full Microcode** | +50 | Very High | Full | 80-120 | 80-120 | ✅ Exact | 25-30 |
| **Plan 5: Minimal Enhancement** | +105 | Medium | None | 300-350* | 300-350* | ⚠️ Partial | 15-20 |

*Plan 5 does NOT match 8087 (keeps 50 iterations, no correction)

---

## Background: 8087 CORDIC Implementation

### Intel 8087 Transcendental Unit Architecture

The Intel 8087 uses a **hybrid CORDIC + correction approach** for FPTAN and FPATAN:

**Algorithm:**
1. **Range Reduction:** Reduce argument to [-π/4, +π/4] for TAN, [0, π/2] for ATAN
2. **CORDIC Phase:** 16 iterations using ROM-based arctangent constants
3. **Correction Phase:** Small rational/polynomial approximation on residual angle
4. **Result Assembly:** Combine CORDIC result with correction

**ROM Constants:**
- 16 values: `atan(2^-n)` for n=0 to 15
- Stored in microcode ROM (shared with other transcendentals)
- High precision: 64-bit mantissa values

**CORDIC Characteristics:**
- **Iterations:** Fixed 16 (deterministic timing)
- **Precision:** Bulk angle reduction to ~2^-16 radians
- **Method:** Shift-and-add (no hardware multiplier needed)

**Correction Phase:**
- **Input:** Residual angle ε after 16 CORDIC iterations (ε < 2^-16)
- **Method:** Rational approximation R(ε) = (a₀ + a₁·ε) / (b₀ + b₁·ε)
- **Precision:** Achieves <1 ULP final error
- **Cycles:** 3-5 additional cycles (using existing mul/div units)

**Why This Works:**
- CORDIC provides **speed**: 16 iterations = bulk reduction
- Correction provides **precision**: Final <1 ULP accuracy
- **Trade-off:** Slightly more complex control logic, but saves ~34 CORDIC iterations

### Current Implementation vs 8087

| Aspect | Current Implementation | Intel 8087 |
|--------|----------------------|------------|
| **Algorithm** | Pure CORDIC (50 iterations) | Hybrid CORDIC (16 iter) + correction |
| **Operations** | SIN, COS, ATAN directly | TAN, ATAN (SIN/COS via identities) |
| **Iterations** | 50 (variable with early term.) | 16 fixed + correction phase |
| **Accuracy** | ~1 ULP (with 50 iterations) | <1 ULP guaranteed (correction) |
| **Cycles (TAN)** | ~350 (SIN/COS + DIV) | ~200-250 (16 CORDIC + correction + assembly) |
| **Cycles (ATAN)** | ~350 (50 iterations) | ~200-300 (16 CORDIC + correction) |
| **Area** | ~300-350 ALMs (wrapper + core) | Estimated ~400-450 ALMs (hybrid approach) |
| **User Interface** | Convenient (direct SIN/COS) | Requires identities for SIN/COS |

---

## Plan 1: Full Hardware Implementation (Hybrid CORDIC + Correction)

### Architecture

**Block Diagram:**
```
┌─────────────────────────────────────────────────────────────┐
│ FPU_CORDIC_Wrapper (Enhanced)                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌────────────────┐   │
│  │ Input        │  │ Range        │  │ FP80 Converter │   │
│  │ Validation   │→ │ Reduction    │→ │ (Shared Module)│   │
│  └──────────────┘  └──────────────┘  └────────────────┘   │
│                                             ↓               │
│                    ┌─────────────────────────────┐          │
│  ┌────────────┐   │ Mode Selection              │          │
│  │ Exception  │   │  - SIN/COS: 50 iter CORDIC  │          │
│  │ Handler    │←──│  - TAN/ATAN: 16 iter CORDIC │          │
│  └────────────┘   │             + Correction     │          │
│                    └─────────────────────────────┘          │
│                                 ↓                           │
│         ┌──────────────┬────────┴────────┬────────────┐    │
│         │              │                 │            │    │
│    ┌────▼────┐   ┌────▼────┐      ┌─────▼──────┐  ┌─▼──┐ │
│    │ CORDIC  │   │ CORDIC  │      │ Correction │  │ FP │ │
│    │ 50-iter │   │ 16-iter │      │ Unit       │  │ Neg│ │
│    │(SIN/COS)│   │(TAN/ATAN│      │ (Rational) │  │    │ │
│    └────┬────┘   └────┬────┘      └─────┬──────┘  └─┬──┘ │
│         │             │                  │            │    │
│         └──────┬──────┴──────────────────┘            │    │
│                │                                      │    │
│         ┌──────▼──────────┐                    ┌─────▼──┐ │
│         │ Output Assembly │                    │ Except │ │
│         │ & Quadrant Fix  │────────────────────│ Flags  │ │
│         └─────────────────┘                    └────────┘ │
└─────────────────────────────────────────────────────────────┘
```

### Implementation Details

#### 1. Dual CORDIC Paths

**Path A: SIN/COS (Unchanged)**
```verilog
// Existing 50-iteration CORDIC for rotation mode (SIN/COS)
localparam NUM_ITERATIONS_SINCOS = 50;

STATE_CORDIC_ITER_SINCOS: begin
    // Current implementation preserved exactly
    // 50 iterations, early termination optional
    // Direct output: cos(θ) ≈ x_cordic, sin(θ) ≈ y_cordic
end
```

**Path B: TAN/ATAN (New - 16 iterations)**
```verilog
// New 16-iteration CORDIC for TAN/ATAN (matches 8087)
localparam NUM_ITERATIONS_TANATAN = 16;

STATE_CORDIC_ITER_TANATAN: begin
    // Reduced iteration count (16 total)
    // Leaves residual error ε < 2^-16
    // Passes residual to correction unit

    // After 16 iterations:
    // - ATAN mode: residual angle in z_cordic
    // - TAN mode: residual in both x,y,z
    if (iteration_count >= NUM_ITERATIONS_TANATAN - 1) begin
        state <= STATE_CORRECTION;
    end
end
```

#### 2. Correction Unit (New Hardware)

**Rational Approximation Module:**
```verilog
module FPU_CORDIC_Correction(
    input wire clk,
    input wire reset,
    input wire enable,
    input wire mode,  // 0=ATAN, 1=TAN

    // Residual after 16 CORDIC iterations
    input wire [79:0] residual_angle,  // ε (very small: |ε| < 2^-16)
    input wire [79:0] cordic_x,        // CORDIC x result
    input wire [79:0] cordic_y,        // CORDIC y result
    input wire [79:0] cordic_z,        // CORDIC z result (angle)

    // Correction output
    output reg [79:0] corrected_result,
    output reg done,
    output reg error,

    // Shared arithmetic unit interface (reuse existing FPU units)
    output reg        mul_req,
    output reg [79:0] mul_a,
    output reg [79:0] mul_b,
    input wire [79:0] mul_result,
    input wire        mul_done,

    output reg        div_req,
    output reg [79:0] div_a,
    output reg [79:0] div_b,
    input wire [79:0] div_result,
    input wire        div_done,

    output reg        add_req,
    output reg [79:0] add_a,
    output reg [79:0] add_b,
    output reg        add_sub,
    input wire [79:0] add_result,
    input wire        add_done
);

    // Rational approximation constants (ROM)
    // For ATAN: R(ε) ≈ (a₀ + a₁·ε) / (b₀ + b₁·ε)
    // For TAN:  R(ε) ≈ (c₀ + c₁·ε) / (d₀ + d₁·ε)

    // ATAN correction: atan(ε) ≈ ε - ε³/3 + ε⁵/5 for small ε
    // Simplified: atan(ε) ≈ ε·(1 - ε²·0.333333)
    localparam FP80_ATAN_C1 = 80'h3FFF_8000000000000000;  // 1.0
    localparam FP80_ATAN_C3 = 80'hBFFD_AAAAAAAAAAA00000;  // -0.33333333...

    // TAN correction: tan(ε) ≈ ε + ε³/3 + 2ε⁵/15 for small ε
    // Simplified: tan(ε) ≈ ε·(1 + ε²·0.333333)
    localparam FP80_TAN_C1 = 80'h3FFF_8000000000000000;   // 1.0
    localparam FP80_TAN_C3 = 80'h3FFD_AAAAAAAAAAA00000;   // +0.33333333...

    reg [3:0] state;
    reg [79:0] epsilon, epsilon_sq, correction_term;

    localparam S_IDLE     = 4'd0;
    localparam S_MUL_E2   = 4'd1;  // ε²
    localparam S_MUL_C3   = 4'd2;  // ε² × coeff
    localparam S_ADD_C1   = 4'd3;  // 1 ± ε²·coeff
    localparam S_MUL_E    = 4'd4;  // ε × (1 ± ε²·coeff)
    localparam S_COMBINE  = 4'd5;  // Add correction to CORDIC result
    localparam S_DONE     = 4'd6;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= S_IDLE;
            // ... reset logic ...
        end else begin
            case (state)
                S_IDLE: begin
                    if (enable) begin
                        epsilon <= residual_angle;
                        state <= S_MUL_E2;
                    end
                end

                S_MUL_E2: begin
                    // Compute ε²
                    mul_req <= 1'b1;
                    mul_a <= epsilon;
                    mul_b <= epsilon;
                    state <= S_WAIT_MUL_E2;
                end

                // ... state machine continues for 5 arithmetic operations ...
                // Total cycles: ~3-5 (depends on mul/div/add latency)

                S_COMBINE: begin
                    // Final: CORDIC_result + correction
                    add_req <= 1'b1;
                    add_a <= (mode == 0) ? cordic_z : cordic_y;  // ATAN or TAN
                    add_b <= correction_term;
                    add_sub <= 1'b0;
                    state <= S_WAIT_COMBINE;
                end

                S_DONE: begin
                    done <= 1'b1;
                    corrected_result <= add_result;
                    if (~enable) state <= S_IDLE;
                end
            endcase
        end
    end
endmodule
```

**Correction Unit Features:**
- **Polynomial/Rational approximation** for residual angle ε
- **Reuses existing FPU arithmetic units** (AddSub, MulDiv)
- **Separate correction paths** for ATAN and TAN
- **Cycle count:** 3-5 cycles (3 multiplies + 2 adds/subs)
- **Area:** ~80-100 ALMs (state machine + ROM constants + muxing)

#### 3. Format Converter Integration

**Replace Functions with Module Instances:**
```verilog
// Add new modes to FPU_Format_Converter_Unified
localparam MODE_FP80_TO_FIXED64 = 4'd10;  // FP80 → Q2.62
localparam MODE_FIXED64_TO_FP80 = 4'd11;  // Q2.62 → FP80

// Instantiate converter for input conversion
FPU_Format_Converter_Unified fp80_to_fixed_conv (
    .clk(clk),
    .reset(reset),
    .enable(fp80_to_fixed_enable),
    .mode(MODE_FP80_TO_FIXED64),
    .fp80_in(angle_reduced),
    .rounding_mode(2'b00),  // Round to nearest
    .uint64_out(angle_fixed),  // Treat as Q2.62
    .done(fp80_to_fixed_done),
    .flag_invalid(conv_invalid),
    .flag_overflow(conv_overflow),
    .flag_underflow(conv_underflow),
    .flag_inexact(conv_inexact)
);

// Instantiate converter for output conversion
FPU_Format_Converter_Unified fixed_to_fp80_conv (
    .clk(clk),
    .reset(reset),
    .enable(fixed_to_fp80_enable),
    .mode(MODE_FIXED64_TO_FP80),
    .uint64_in(cordic_result),  // Treat as Q2.62
    .rounding_mode(2'b00),
    .fp80_out(result_fp80),
    .done(fixed_to_fp80_done),
    .flag_invalid(conv_invalid_out),
    .flag_overflow(conv_overflow_out),
    .flag_underflow(conv_underflow_out),
    .flag_inexact(conv_inexact_out)
);
```

**Modifications to Format Converter:**
Add two new conversion modes (Q2.62 fixed-point ↔ FP80):

```verilog
// In FPU_Format_Converter_Unified.v, add cases:

case (mode)
    // ... existing modes ...

    MODE_FP80_TO_FIXED64: begin
        // FP80 → Q2.62 fixed-point
        // Extract FP80 components
        src_sign = fp80_in[79];
        src_exp = fp80_in[78:64];
        src_mant = fp80_in[63:0];

        // Compute shift for Q2.62 format
        // Q2.62 has binary point after bit 62
        // Target: mantissa × 2^(exp - bias - 1 + 62)
        shift_amount = src_exp - 15'd16384;  // exp - bias - 1 + 62 = exp - 16322

        if (shift_amount >= 0) begin
            shifted_mant = src_mant << shift_amount;
        end else begin
            // Right shift with rounding
            shifted_mant = round_shift_right(src_mant, -shift_amount, rounding_mode);
            flag_inexact = 1'b1;
        end

        // Apply sign
        uint64_out = src_sign ? -shifted_mant : shifted_mant;
        done = 1'b1;
    end

    MODE_FIXED64_TO_FP80: begin
        // Q2.62 fixed-point → FP80
        // Q2.62: value = uint64_in / 2^62

        if (uint64_in == 0) begin
            fp80_out = FP80_ZERO;
        end else begin
            dst_sign = uint64_in[63];
            abs_val = dst_sign ? -uint64_in : uint64_in;

            // Count leading zeros
            leading_zeros = count_lz(abs_val);

            // Normalize
            dst_mant = abs_val << leading_zeros;

            // Compute exponent
            // FP80: value = mant × 2^(exp - bias - 63)
            // Q2.62: value = abs_val × 2^-62
            // So: mant × 2^(exp - 16383 - 63) = (abs_val << lz) × 2^-62
            //     exp = 16384 - lz  (since bias=16383, -63+62=-1)
            dst_exp = 15'd16384 - leading_zeros;

            fp80_out = {dst_sign, dst_exp, dst_mant};
        end
        done = 1'b1;
    end
endcase
```

**Area Impact:** +40-50 ALMs (new mode logic in converter)
**Latency:** 1-2 cycles (pipelined converter)

#### 4. Proper FP80 Negate Function

```verilog
function [79:0] fp80_negate;
    input [79:0] value;
    reg sign;
    reg [14:0] exponent;
    reg [63:0] mantissa;
    begin
        sign = value[79];
        exponent = value[78:64];
        mantissa = value[63:0];

        // Check for zero
        if (exponent == 15'd0 && mantissa == 64'd0) begin
            // Signed zero: flip sign
            fp80_negate = {~sign, 15'd0, 64'd0};
        end
        // Check for NaN
        else if (exponent == 15'h7FFF && mantissa[63] == 1'b0) begin
            // NaN: flip sign, preserve payload (QNaN if SNaN)
            fp80_negate = {~sign, exponent, mantissa | 64'h4000000000000000};
        end
        // Check for Infinity
        else if (exponent == 15'h7FFF && mantissa == 64'h8000000000000000) begin
            // Infinity: flip sign
            fp80_negate = {~sign, exponent, mantissa};
        end
        // Normal or denormal
        else begin
            // Just flip sign bit
            fp80_negate = {~sign, exponent, mantissa};
        end
    end
endfunction
```

**Area Impact:** +15-20 ALMs
**Latency:** 0 cycles (combinational)

#### 5. Comprehensive Exception Handling

```verilog
// Add exception flag outputs
output reg flag_invalid,    // Invalid operation (NaN, Inf, |angle| > 2^63)
output reg flag_overflow,   // Overflow in conversion
output reg flag_underflow,  // Underflow in conversion
output reg flag_inexact;    // Rounding occurred

// 8087 Indefinite NaN constant
localparam FP80_INDEFINITE = 80'hFFFF_C000000000000000;

// Input validation state
STATE_VALIDATE_INPUT: begin
    reg [14:0] exp;
    reg [63:0] mant;

    exp = angle_in[78:64];
    mant = angle_in[63:0];

    // Check for NaN
    if (exp == 15'h7FFF && mant[63] == 1'b0) begin
        flag_invalid <= 1'b1;
        result_primary <= FP80_INDEFINITE;
        error <= 1'b1;
        state <= STATE_DONE;
    end
    // Check for Infinity
    else if (exp == 15'h7FFF && mant == 64'h8000000000000000) begin
        flag_invalid <= 1'b1;
        result_primary <= FP80_INDEFINITE;
        error <= 1'b1;
        state <= STATE_DONE;
    end
    // Check for argument too large (8087 limit: |x| > 2^63)
    else if (exp >= 15'h3FFF + 63) begin
        flag_invalid <= 1'b1;
        result_primary <= FP80_INDEFINITE;
        error <= 1'b1;
        state <= STATE_DONE;
    end
    else begin
        // Input valid, proceed
        state <= STATE_RANGE_REDUCE;
    end
end
```

**Area Impact:** +40-50 ALMs
**Latency:** +1 cycle (validation state)

### State Machine Flow

**Enhanced State Machine:**
```
IDLE
  ↓
VALIDATE_INPUT  [New: +1 cycle, checks NaN/Inf/overflow]
  ↓
ROUTE_OPERATION  [New: determines SIN/COS vs TAN/ATAN path]
  ↓
┌──────────────────┬──────────────────┐
│                  │                  │
SIN/COS PATH       TAN/ATAN PATH
│                  │
RANGE_REDUCE       RANGE_REDUCE
  ↓                  ↓
CONVERT_INPUT      CONVERT_INPUT [Uses format converter: +1-2 cycles]
  ↓                  ↓
CORDIC_INIT        CORDIC_INIT
  ↓                  ↓
CORDIC_50_ITER     CORDIC_16_ITER [New: only 16 iterations]
  ↓                  ↓
CONVERT_OUTPUT     CORRECTION [New: +3-5 cycles for rational approx]
  ↓                  ↓
QUAD_CORRECT       CONVERT_OUTPUT [Uses format converter: +1-2 cycles]
  ↓                  ↓
DONE               QUAD_CORRECT
                     ↓
                   DONE
```

### Performance Analysis

**Cycle Counts:**

| Operation | Current | Plan 1 (Full HW) | 8087 Reference |
|-----------|---------|------------------|----------------|
| **FSIN**  | 50-55 (50 iter) | 50-55 (unchanged) | 200-300 |
| **FCOS**  | 50-55 (50 iter) | 50-55 (unchanged) | 200-300 |
| **FSINCOS** | 50-55 | 50-55 (unchanged) | 250-350 |
| **FPTAN** | ~350 (50 iter + div) | **35-40** (16 iter + correction) | 200-250 |
| **FPATAN** | ~350 (50 iter) | **35-40** (16 iter + correction) | 200-300 |

**Breakdown for TAN/ATAN (Plan 1):**
- Validation: 1 cycle
- Range reduction: 5-8 cycles
- FP80 → Fixed conversion: 1-2 cycles
- CORDIC 16 iterations: 16 cycles
- Correction (rational approx): 3-5 cycles
- Fixed → FP80 conversion: 1-2 cycles
- Quadrant correction: 1 cycle
- **Total: 28-37 cycles** (average ~35 cycles)

**Speedup:**
- **TAN:** 350 → 35 cycles = **10× faster**
- **ATAN:** 350 → 35 cycles = **10× faster**

### Area Analysis

**Hardware Additions:**

| Component | ALMs | Description |
|-----------|------|-------------|
| **Correction Unit** | +80-100 | State machine, ROM constants, muxing |
| **Format Converter Mods** | +40-50 | MODE_FP80_TO_FIXED64, MODE_FIXED64_TO_FP80 |
| **FP80 Negate Function** | +15-20 | Special value handling logic |
| **Exception Handling** | +40-50 | Validation, flag generation |
| **Dual Path Routing** | +20-25 | Mode selection, path muxes |
| **Correction ROM Constants** | +10-15 | 4 FP80 constants (ATAN/TAN coefficients) |
| **Shared Unit Arbitration** | +30-40 | Request logic for mul/div/add sharing |
| **TOTAL** | **+235-300** | **Average: ~285 ALMs** |

**Percentage of Total FPU:**
- Current FPU: ~43,000 ALMs (100%)
- CORDIC Wrapper current: ~350 ALMs (0.8%)
- Plan 1 additions: ~285 ALMs (0.7%)
- **New CORDIC total: ~635 ALMs (1.5% of FPU)**

### Pros and Cons

#### ✅ Pros

1. **Exact 8087 Match:**
   - TAN/ATAN use 16 iterations + correction (identical to 8087)
   - Same accuracy (<1 ULP guaranteed)
   - Same deterministic timing

2. **Best Performance:**
   - TAN: **10× speedup** (350 → 35 cycles)
   - ATAN: **10× speedup** (350 → 35 cycles)
   - SIN/COS: Unchanged (optimal for direct computation)

3. **Full IEEE 754 Compliance:**
   - Proper FP80 conversions (rounding, denormals)
   - Comprehensive exception flags
   - Special value handling (NaN, Inf, signed zero)

4. **Preserves SIN/COS:**
   - No changes to existing rotation mode CORDIC
   - Maintains current accuracy and performance
   - Backward compatible

5. **Deterministic Timing:**
   - Fixed iteration count for TAN/ATAN (like 8087)
   - Predictable worst-case latency
   - No variable early termination complexity

#### ❌ Cons

1. **Highest Hardware Cost:**
   - +285 ALMs (highest of all plans)
   - Requires dedicated correction unit
   - Additional ROM for correction constants

2. **Complex Integration:**
   - Dual CORDIC paths (50-iter and 16-iter)
   - Shared arithmetic unit arbitration
   - More state machine complexity
   - More potential for timing closure issues

3. **Longer Development Time:**
   - 40-50 engineering hours
   - New correction unit design/verification
   - Format converter modifications
   - Extensive testing required

4. **Unit Sharing Contention:**
   - Correction unit needs mul/div/add access
   - Potential conflicts with other FPU operations
   - Requires priority arbitration logic

5. **Not Modular:**
   - Correction logic tightly coupled to CORDIC
   - Harder to update/modify later
   - Less reusable for other operations

### Development Effort Estimate

**Total: 40-50 hours (5-6 days)**

| Task | Hours | Description |
|------|-------|-------------|
| **Correction Unit Design** | 12-15 | Rational approximation algorithm, state machine |
| **Format Converter Mods** | 4-6 | Add Q2.62 ↔ FP80 modes |
| **Dual Path Routing** | 6-8 | Mode selection, path muxing, arbiter |
| **Exception Handling** | 4-6 | Validation, flag generation |
| **FP80 Negate** | 2-3 | Special value handling |
| **Integration & Debug** | 8-10 | Wire up all components, fix bugs |
| **Verification** | 4-6 | Unit tests, compare against 8087 |
| **TOTAL** | **40-54** | **~1 week** |

---

## Plan 2: Heavy Unit Reuse (Minimal New Hardware)

### Architecture

**Strategy:** Maximize reuse of existing FPU modules, minimize new hardware.

**Key Principles:**
1. Use existing `FPU_Format_Converter_Unified` without modifications
2. Reuse existing `FPU_IEEE754_AddSub` and `FPU_IEEE754_MulDiv_Unified`
3. Implement correction via state machine sequencing (no dedicated correction unit)
4. Keep dual CORDIC paths (50-iter and 16-iter)

**Block Diagram:**
```
┌────────────────────────────────────────────────────┐
│ FPU_CORDIC_Wrapper (Unit Reuse Approach)          │
├────────────────────────────────────────────────────┤
│                                                    │
│  ┌──────────────┐  ┌──────────────┐              │
│  │ Input        │  │ Range        │              │
│  │ Validation   │→ │ Reduction    │              │
│  └──────────────┘  └──────────────┘              │
│                           ↓                        │
│              ┌────────────────────────┐           │
│              │ CORDIC Path Selection  │           │
│              │ SIN/COS: 50 iterations │           │
│              │ TAN/ATAN: 16 iterations│           │
│              └────────────────────────┘           │
│                           ↓                        │
│         ┌────────────────────────────┐            │
│         │ Correction State Machine   │            │
│         │ (Reuses Existing Units)    │            │
│         │   ┌─────────────────┐      │            │
│         │   │ Ext AddSub Req  │──────┼───────────→│ To FPU_IEEE754_AddSub
│         │   │ Ext MulDiv Req  │──────┼───────────→│ To FPU_IEEE754_MulDiv
│         │   └─────────────────┘      │            │
│         └────────────────────────────┘            │
│                           ↓                        │
│              ┌──────────────────────┐             │
│              │ Output Assembly      │             │
│              │ & Exception Handling │             │
│              └──────────────────────┘             │
└────────────────────────────────────────────────────┘
```

### Implementation Details

#### 1. No Dedicated Correction Unit

Instead of a separate correction module, implement correction via **extended state machine** in the CORDIC wrapper:

```verilog
// Additional states for correction phase
localparam STATE_CORR_MUL_E2   = 4'd10;  // Multiply ε × ε
localparam STATE_CORR_MUL_C3   = 4'd11;  // Multiply ε² × coeff
localparam STATE_CORR_ADD_C1   = 4'd12;  // Add/sub 1 ± ε²·coeff
localparam STATE_CORR_MUL_E    = 4'd13;  // Multiply ε × (...)
localparam STATE_CORR_COMBINE  = 4'd14;  // Combine with CORDIC result

// Correction constants stored in wrapper (no separate ROM module)
reg [79:0] correction_constants [0:3];
initial begin
    correction_constants[0] = 80'h3FFF_8000000000000000;  // ATAN C1: 1.0
    correction_constants[1] = 80'hBFFD_AAAAAAAAAAA00000;  // ATAN C3: -0.333...
    correction_constants[2] = 80'h3FFF_8000000000000000;  // TAN C1: 1.0
    correction_constants[3] = 80'h3FFD_AAAAAAAAAAA00000;  // TAN C3: +0.333...
end

// Extended state machine
STATE_CORDIC_ITER_TANATAN: begin
    // 16 iterations for TAN/ATAN
    if (iteration_count >= 15) begin
        // Store residual
        residual_angle <= z_cordic;  // Or compute from x,y for TAN
        state <= STATE_CORR_MUL_E2;
    end else begin
        iteration_count <= iteration_count + 1;
    end
end

STATE_CORR_MUL_E2: begin
    // Request ε²: use shared MulDiv unit
    ext_muldiv_req <= 1'b1;
    ext_muldiv_op <= 1'b0;  // Multiply
    ext_muldiv_a <= residual_angle;
    ext_muldiv_b <= residual_angle;
    state <= STATE_CORR_WAIT_MUL_E2;
end

STATE_CORR_WAIT_MUL_E2: begin
    ext_muldiv_req <= 1'b0;
    if (ext_muldiv_done) begin
        epsilon_squared <= ext_muldiv_result;
        state <= STATE_CORR_MUL_C3;
    end
end

STATE_CORR_MUL_C3: begin
    // Compute ε² × coeff
    ext_muldiv_req <= 1'b1;
    ext_muldiv_op <= 1'b0;
    ext_muldiv_a <= epsilon_squared;
    ext_muldiv_b <= (cordic_mode == MODE_ATAN) ?
                    correction_constants[1] :  // ATAN: -0.333
                    correction_constants[3];   // TAN: +0.333
    state <= STATE_CORR_WAIT_MUL_C3;
end

// ... continue for remaining correction steps ...
// Total: 5 arithmetic operations using shared units
```

**Advantage:** No dedicated correction hardware
**Disadvantage:** Longer latency (shared units may be busy)

#### 2. Reuse Format Converter As-Is

**Option A: Use Existing INT64 Modes (Workaround)**

The format converter already has `MODE_FP80_TO_INT64` and `MODE_INT64_TO_FP80` (via UINT64 modes). Use these with scaling:

```verilog
// FP80 → Q2.62 conversion workaround
STATE_CONVERT_INPUT: begin
    // Step 1: Multiply angle by 2^62 to shift to integer range
    ext_muldiv_req <= 1'b1;
    ext_muldiv_op <= 1'b0;  // Multiply
    ext_muldiv_a <= angle_reduced;
    ext_muldiv_b <= 80'h403E_8000000000000000;  // 2^62 in FP80
    state <= STATE_WAIT_SCALE_MUL;
end

STATE_WAIT_SCALE_MUL: begin
    ext_muldiv_req <= 1'b0;
    if (ext_muldiv_done) begin
        scaled_angle <= ext_muldiv_result;
        state <= STATE_FP80_TO_INT;
    end
end

STATE_FP80_TO_INT: begin
    // Step 2: Convert scaled FP80 to INT64 using existing mode
    fmt_conv_enable <= 1'b1;
    fmt_conv_mode <= MODE_FP80_TO_UINT64;
    fmt_conv_fp80_in <= scaled_angle;
    state <= STATE_WAIT_CONV;
end

// Reverse for output: INT64 → FP80 → divide by 2^62
```

**Advantage:** No format converter modifications
**Disadvantage:** +2 arithmetic operations per conversion (mul/div by 2^62)

**Option B: Modify Format Converter (Simpler, recommended)**

Still simpler than Plan 1 because we reuse the converter's infrastructure:

```verilog
// Add just the two Q2.62 modes (same as Plan 1)
// Minimal change, big payoff
MODE_FP80_TO_FIXED64: begin
    // ~20 lines of code
end

MODE_FIXED64_TO_FP80: begin
    // ~20 lines of code
end
```

**Area Impact:** +40-50 ALMs (same as Plan 1)
**Latency:** 1-2 cycles (same as Plan 1)

**Recommendation:** Use Option B (slight modification) for better performance.

#### 3. Shared Unit Request Interface

```verilog
// External arithmetic unit interface (same as FPU_Transcendental)
output reg        ext_addsub_req,
output reg [79:0] ext_addsub_a,
output reg [79:0] ext_addsub_b,
output reg        ext_addsub_sub,
input wire [79:0] ext_addsub_result,
input wire        ext_addsub_done,
input wire        ext_addsub_invalid,
// ... other flags ...

output reg        ext_muldiv_req,
output reg        ext_muldiv_op,  // 0=mul, 1=div
output reg [79:0] ext_muldiv_a,
output reg [79:0] ext_muldiv_b,
input wire [79:0] ext_muldiv_result,
input wire        ext_muldiv_done,
input wire        ext_muldiv_invalid,
// ... other flags ...
```

**Integration:**
The CORDIC wrapper connects to the **same shared arithmetic units** already used by `FPU_Transcendental`:

```
                      ┌─────────────────────┐
                      │ FPU_ArithmeticUnit  │
                      ├─────────────────────┤
                      │ FPU_IEEE754_AddSub  │
                      │ FPU_IEEE754_MulDiv  │
                      └─────────────────────┘
                                ↑
                 ┌──────────────┼──────────────┐
                 │              │              │
         ┌───────▼──────┐  ┌────▼───────┐  ┌──▼──────────────┐
         │ FPU_Trans-   │  │ FPU_CORDIC │  │ Other FPU       │
         │ cendental    │  │ _Wrapper   │  │ Operations      │
         └──────────────┘  └────────────┘  └─────────────────┘
```

**Arbitration:** Priority arbiter in FPU_Core handles conflicts.

### Performance Analysis

**Cycle Counts:**

| Operation | Current | Plan 2 (Heavy Reuse) | Plan 1 (Full HW) | 8087 |
|-----------|---------|----------------------|------------------|------|
| **FSIN**  | 50-55   | 50-55 (unchanged)    | 50-55            | 200-300 |
| **FCOS**  | 50-55   | 50-55 (unchanged)    | 50-55            | 200-300 |
| **FSINCOS** | 50-55 | 50-55 (unchanged)    | 50-55            | 250-350 |
| **FPTAN** | ~350    | **50-70**            | **35-40**        | 200-250 |
| **FPATAN** | ~350   | **50-70**            | **35-40**        | 200-300 |

**Breakdown for TAN/ATAN (Plan 2):**
- Validation: 1 cycle
- Range reduction: 5-8 cycles
- FP80 → Fixed conversion: 1-2 cycles (or +2 if using workaround)
- CORDIC 16 iterations: 16 cycles
- Correction (5 ops via shared units): **15-30 cycles** (depends on contention)
  - Each mul/div: 3-6 cycles (shared unit latency)
  - If no contention: 5 ops × 3 cycles = 15 cycles
  - If high contention: 5 ops × 6 cycles = 30 cycles
- Fixed → FP80 conversion: 1-2 cycles (or +2 if using workaround)
- Quadrant correction: 1 cycle
- **Total: 40-62 cycles** (average ~50 cycles, worst ~70 cycles)

**Speedup:**
- **TAN:** 350 → 50-70 cycles = **5-7× faster**
- **ATAN:** 350 → 50-70 cycles = **5-7× faster**

**Performance vs Plan 1:**
- Plan 1: 35-40 cycles (dedicated correction unit, no contention)
- Plan 2: 50-70 cycles (shared units, contention possible)
- **Difference: +15-30 cycles slower** (but still 5-7× faster than current)

### Area Analysis

**Hardware Additions:**

| Component | ALMs | Description |
|-----------|------|-------------|
| **Correction State Machine** | +30-40 | 5 additional states, sequencing logic |
| **Correction Constants ROM** | +10-15 | 4 FP80 constants (inline in wrapper) |
| **Format Converter Mods** | +40-50 | MODE_FP80_TO_FIXED64, MODE_FIXED64_TO_FP80 |
| **FP80 Negate Function** | +15-20 | Special value handling logic |
| **Exception Handling** | +40-50 | Validation, flag generation |
| **Dual Path Routing** | +20-25 | Mode selection, path muxes |
| **Shared Unit Interface** | +10-15 | Request/response muxing |
| **TOTAL** | **+165-215** | **Average: ~190 ALMs** |

**Note:** NO dedicated correction unit (saves ~80-100 ALMs vs Plan 1)

**Percentage of Total FPU:**
- Current FPU: ~43,000 ALMs (100%)
- Plan 2 additions: ~190 ALMs (0.4%)
- **New CORDIC total: ~540 ALMs (1.3% of FPU)**

### Pros and Cons

#### ✅ Pros

1. **Lowest Hardware Cost:**
   - +190 ALMs (33% less than Plan 1)
   - Saves ~95 ALMs by eliminating dedicated correction unit
   - Still achieves 8087 accuracy

2. **Maximum Reuse:**
   - Uses existing AddSub/MulDiv units (proven, tested)
   - Minimal modifications to format converter
   - Leverages existing FPU infrastructure

3. **Good Performance:**
   - TAN/ATAN: 5-7× speedup (vs 10× for Plan 1)
   - Still much faster than current implementation
   - Acceptable for most use cases

4. **Simpler Integration:**
   - No new major hardware modules
   - Uses same shared unit interface as FPU_Transcendental
   - Easier to verify and debug

5. **Exact 8087 Algorithm:**
   - Same 16 iterations + correction approach
   - Same accuracy (<1 ULP)
   - Matches 8087 behavior exactly

#### ❌ Cons

1. **Slower Than Plan 1:**
   - +15-30 cycles slower due to shared unit latency
   - Variable performance depending on contention
   - Not deterministic (depends on FPU load)

2. **Shared Unit Contention:**
   - Correction may wait for AddSub/MulDiv availability
   - Other FPU operations may be delayed
   - Requires priority arbitration

3. **More State Machine Complexity:**
   - 5 additional states for correction sequencing
   - More complex control flow
   - Harder to read/maintain

4. **Non-Modular Correction:**
   - Correction logic embedded in wrapper state machine
   - Less reusable for other operations
   - Harder to update correction algorithm later

5. **Still Significant Effort:**
   - 30-40 hours development time
   - Testing contention scenarios
   - Verifying timing under load

### Development Effort Estimate

**Total: 30-40 hours (4-5 days)**

| Task | Hours | Description |
|------|-------|-------------|
| **Correction State Machine** | 8-10 | 5 states, request sequencing |
| **Format Converter Mods** | 4-6 | Add Q2.62 ↔ FP80 modes |
| **Dual Path Routing** | 6-8 | Mode selection, path muxing |
| **Exception Handling** | 4-6 | Validation, flag generation |
| **FP80 Negate** | 2-3 | Special value handling |
| **Shared Unit Interface** | 4-6 | Request/response logic |
| **Integration & Debug** | 6-8 | Wire up, fix contention issues |
| **Verification** | 4-6 | Test correction accuracy, measure contention |
| **TOTAL** | **38-53** | **~1 week** |

---

## Plan 3: Hybrid Hardware + Microcode

### Architecture

**Strategy:** Offload correction phase to FPU microcode, keep hardware CORDIC.

**Division of Labor:**
- **Hardware:** CORDIC iterations (16 for TAN/ATAN, 50 for SIN/COS)
- **Microcode:** Correction polynomial evaluation, result assembly

**Key Insight:** The FPU already has a powerful microsequencer that can perform arithmetic operations. Use it for the correction phase instead of building dedicated hardware.

**Block Diagram:**
```
┌─────────────────────────────────────────────────────┐
│ FPU_CORDIC_Wrapper (Hybrid Approach)                │
├─────────────────────────────────────────────────────┤
│                                                     │
│  ┌──────────────┐  ┌──────────────┐  ┌───────────┐ │
│  │ Input        │  │ Range        │  │ CORDIC    │ │
│  │ Validation   │→ │ Reduction    │→ │ 16 or 50  │ │
│  │              │  │              │  │ iterations│ │
│  └──────────────┘  └──────────────┘  └─────┬─────┘ │
│                                             │       │
│                    ┌────────────────────────┘       │
│                    │                                │
│         ┌──────────▼─────────┐                      │
│         │ Microcode Handoff  │                      │
│         │ (For TAN/ATAN only)│                      │
│         └──────────┬─────────┘                      │
│                    │                                │
└────────────────────┼────────────────────────────────┘
                     │
                     ↓
         ┌───────────────────────┐
         │ FPU Microsequencer    │
         ├───────────────────────┤
         │ Correction Microcode: │
         │  1. Load ε (residual) │
         │  2. FP_MUL ε, ε       │  (ε²)
         │  3. FP_MUL ε², coeff  │  (ε²·c)
         │  4. FP_ADD 1, (ε²·c)  │  (1±ε²·c)
         │  5. FP_MUL ε, (...)   │  correction
         │  6. FP_ADD CORDIC, c  │  final result
         │  7. Return to stack   │
         └───────────────────────┘
```

### Implementation Details

#### 1. CORDIC Wrapper Modifications

**Hardware stays simple:**
```verilog
// After 16 CORDIC iterations for TAN/ATAN, signal microcode takeover
STATE_CORDIC_ITER_TANATAN: begin
    if (iteration_count >= 15) begin
        // Store intermediate results in special registers
        cordic_result_x <= x_cordic;
        cordic_result_y <= y_cordic;
        cordic_result_z <= z_cordic;  // residual angle ε

        // Signal microcode continuation needed
        microcode_continue <= 1'b1;
        microcode_op <= (cordic_mode == MODE_ATAN) ?
                        MICROCODE_ATAN_CORRECTION :
                        MICROCODE_TAN_CORRECTION;

        state <= STATE_MICROCODE_HANDOFF;
    end else begin
        iteration_count <= iteration_count + 1;
    end
end

STATE_MICROCODE_HANDOFF: begin
    // Wait for microcode to signal completion
    if (microcode_done) begin
        // Microcode has stored final result on FPU stack
        // CORDIC wrapper just signals done
        done <= 1'b1;
        state <= STATE_DONE;
    end
end
```

**Interface additions:**
```verilog
// Microcode interface
output reg        microcode_continue,  // Signal microcode takeover
output reg [3:0]  microcode_op,        // Which correction to run
output reg [79:0] cordic_result_x,     // Intermediate x
output reg [79:0] cordic_result_y,     // Intermediate y
output reg [79:0] cordic_result_z,     // Residual angle ε
input wire        microcode_done       // Microcode finished
```

#### 2. FPU Microcode Implementation

**New microcode routines in FPU microsequencer:**

**File:** `Quartus/rtl/FPU8087/microcode/cordic_correction.us`

```assembly
# CORDIC ATAN Correction Microcode
# Input: ST(0) = residual angle ε (from CORDIC z register)
#        ST(1) = CORDIC atan result (partial)
# Output: ST(0) = corrected atan result

microcode atan_correction_cordic {
    # Constants in microcode ROM:
    # C1 = 1.0
    # C3 = -0.333333... (for atan correction)

    # Algorithm: atan(ε) ≈ ε·(1 - ε²/3)

    # ST(0) = ε
    # ST(1) = CORDIC_result

    # 1. Compute ε²
    FLD ST(0);           # Duplicate ε → ST(0)=ε, ST(1)=ε, ST(2)=CORDIC
    FMUL ST(0), ST(1);   # ST(0) = ε²

    # 2. Compute ε² × (-1/3)
    FLD @ATAN_C3;        # Load constant -0.333... → ST(0)=-1/3, ST(1)=ε²
    FMUL ST(1), ST(0);   # ST(1) = ε² × (-1/3)
    FSTP ST(0);          # Pop → ST(0) = ε²×(-1/3), ST(1)=ε, ST(2)=CORDIC

    # 3. Add 1
    FLD @FP80_ONE;       # Load 1.0 → ST(0)=1, ST(1)=ε²×(-1/3)
    FADD ST(1), ST(0);   # ST(1) = 1 + ε²×(-1/3) = 1 - ε²/3
    FSTP ST(0);          # Pop → ST(0) = 1-ε²/3, ST(1)=ε, ST(2)=CORDIC

    # 4. Multiply by ε
    FMUL ST(1), ST(0);   # ST(1) = ε × (1-ε²/3) = correction
    FSTP ST(0);          # Pop → ST(0) = correction, ST(1)=ε, ST(2)=CORDIC

    # 5. Add to CORDIC result
    FADD ST(2), ST(0);   # ST(2) = CORDIC + correction = final result
    FSTP ST(0);          # Pop → ST(0)=?, ST(1)=ε, ST(2)=final
    FSTP ST(0);          # Pop → ST(0)=ε, ST(1)=final
    FSTP ST(0);          # Pop → ST(0)=final

    # Done - final result in ST(0)
    RET;
}

# CORDIC TAN Correction Microcode
# Similar structure, but uses +0.333... coefficient

microcode tan_correction_cordic {
    # Algorithm: tan(ε) ≈ ε·(1 + ε²/3)

    # ... similar to atan_correction but with positive coefficient ...

    FLD ST(0);           # Duplicate ε
    FMUL ST(0), ST(1);   # ε²
    FLD @TAN_C3;         # Load +0.333...
    FMUL ST(1), ST(0);   # ε² × (+1/3)
    FSTP ST(0);
    FLD @FP80_ONE;       # Load 1.0
    FADD ST(1), ST(0);   # 1 + ε²/3
    FSTP ST(0);
    FMUL ST(1), ST(0);   # ε × (1+ε²/3)
    FSTP ST(0);
    FADD ST(2), ST(0);   # CORDIC + correction
    FSTP ST(0);
    FSTP ST(0);
    FSTP ST(0);
    RET;
}
```

**Constants stored in microcode ROM:**
```verilog
// In FPU microcode constant table
ROM_CONSTANT[0x100] = 80'h3FFF_8000000000000000;  // FP80_ONE
ROM_CONSTANT[0x101] = 80'hBFFD_AAAAAAAAAAA00000;  // ATAN_C3 (-0.333...)
ROM_CONSTANT[0x102] = 80'h3FFD_AAAAAAAAAAA00000;  // TAN_C3 (+0.333...)
```

#### 3. FPU Core Integration

**In FPU_Core.v:**
```verilog
// Detect CORDIC microcode continuation signal
always @(posedge clk) begin
    if (cordic_microcode_continue) begin
        // Push CORDIC results onto FPU stack
        push_stack(cordic_result_z);      // ST(0) = residual ε
        push_stack(cordic_result_partial); // ST(1) = CORDIC result

        // Jump to correction microcode
        if (cordic_microcode_op == MICROCODE_ATAN_CORRECTION) begin
            microcode_pc <= ADDR_ATAN_CORRECTION_CORDIC;  // e.g., 0x0180
        end else if (cordic_microcode_op == MICROCODE_TAN_CORRECTION) begin
            microcode_pc <= ADDR_TAN_CORRECTION_CORDIC;   // e.g., 0x0190
        end

        // Execute microcode
        microcode_execute <= 1'b1;
    end

    // When microcode returns
    if (microcode_ret && microcode_pc_return_address == ADDR_CORDIC_CONTINUE) begin
        // Signal CORDIC wrapper that correction is done
        cordic_microcode_done <= 1'b1;

        // Result is now in ST(0), ready for CPU to read
    end
end
```

### Performance Analysis

**Cycle Counts:**

| Operation | Current | Plan 3 (Hybrid) | Plan 1 (Full HW) | Plan 2 (Reuse) | 8087 |
|-----------|---------|-----------------|------------------|----------------|------|
| **FSIN**  | 50-55   | 50-55           | 50-55            | 50-55          | 200-300 |
| **FCOS**  | 50-55   | 50-55           | 50-55            | 50-55          | 200-300 |
| **FSINCOS** | 50-55 | 50-55           | 50-55            | 50-55          | 250-350 |
| **FPTAN** | ~350    | **45-60**       | **35-40**        | **50-70**      | 200-250 |
| **FPATAN** | ~350   | **45-60**       | **35-40**        | **50-70**      | 200-300 |

**Breakdown for TAN/ATAN (Plan 3):**
- Validation: 1 cycle
- Range reduction: 5-8 cycles
- FP80 → Fixed conversion: 1-2 cycles
- CORDIC 16 iterations: 16 cycles
- Microcode handoff: 2-3 cycles (push stack, jump)
- **Microcode correction:** **15-25 cycles**
  - FLD/FSTP (stack ops): 1 cycle each × 7 ops = 7 cycles
  - FMUL: 3-4 cycles × 3 ops = 9-12 cycles
  - FADD: 2-3 cycles × 2 ops = 4-6 cycles
  - Total: 20-25 cycles
- Fixed → FP80 conversion: 1-2 cycles
- Quadrant correction: 1 cycle
- **Total: 43-60 cycles** (average ~50 cycles)

**Speedup:**
- **TAN:** 350 → 45-60 cycles = **6-8× faster**
- **ATAN:** 350 → 45-60 cycles = **6-8× faster**

**Performance vs Other Plans:**
- Plan 1 (Full HW): 35-40 cycles (fastest, dedicated hardware)
- Plan 2 (Reuse): 50-70 cycles (shared units, contention)
- **Plan 3 (Hybrid): 45-60 cycles (middle ground, no contention)**

### Area Analysis

**Hardware Additions:**

| Component | ALMs | Description |
|-----------|------|-------------|
| **Microcode Interface** | +20-30 | Handoff signals, result registers |
| **Format Converter Mods** | +40-50 | MODE_FP80_TO_FIXED64, MODE_FIXED64_TO_FP80 |
| **FP80 Negate Function** | +15-20 | Special value handling logic |
| **Exception Handling** | +40-50 | Validation, flag generation |
| **Dual Path Routing** | +20-25 | Mode selection, path muxes |
| **Microcode ROM Constants** | +5-10 | 3 FP80 constants (in microcode ROM) |
| **FPU Core Handoff Logic** | +10-15 | Stack push, PC jump, return |
| **TOTAL** | **+150-200** | **Average: ~175 ALMs** |

**Microcode ROM:**
- Correction routines: ~20-30 microinstructions (already allocated space)
- Constants: 3 × 80 bits = 240 bits (trivial)

**Note:** NO dedicated correction hardware (saves ~80-100 ALMs vs Plan 1)
**Note:** NO shared unit contention (saves complexity vs Plan 2)

**Percentage of Total FPU:**
- Current FPU: ~43,000 ALMs (100%)
- Plan 3 additions: ~175 ALMs (0.4%)
- **New CORDIC total: ~525 ALMs (1.2% of FPU)**

### Pros and Cons

#### ✅ Pros

1. **Low Hardware Cost:**
   - +175 ALMs (between Plan 2 and Plan 1)
   - No dedicated correction unit (saves 80-100 ALMs)
   - Minimal ROM overhead

2. **Good Performance:**
   - TAN/ATAN: 6-8× speedup
   - Faster than Plan 2 (no shared unit contention)
   - Close to Plan 1 (only +10-20 cycles slower)

3. **No Shared Unit Contention:**
   - Microcode has dedicated execution path
   - Doesn't block other FPU operations
   - Deterministic performance

4. **Leverages Existing Microcode Infrastructure:**
   - FPU microsequencer already exists and works
   - Correction is simple microcode (20-30 instructions)
   - Easy to update/tune correction algorithm

5. **Exact 8087 Match:**
   - Same 16 iterations + correction approach
   - Same accuracy (<1 ULP)
   - Matches 8087 behavior

6. **Flexible and Maintainable:**
   - Correction algorithm in microcode (easy to modify)
   - Can add more sophisticated corrections later
   - No hardware changes needed for algorithm updates

#### ❌ Cons

1. **Microcode Complexity:**
   - Requires FPU microassembler knowledge
   - More complex debugging (hardware + microcode)
   - Stack management overhead

2. **Slower Than Plan 1:**
   - +10-20 cycles slower due to microcode overhead
   - Stack push/pop operations add latency
   - Not as fast as dedicated hardware

3. **Tight Coupling:**
   - CORDIC wrapper depends on FPU microsequencer
   - Can't use CORDIC independently
   - More integration complexity

4. **Microcode ROM Space:**
   - Uses microcode ROM (limited resource)
   - ~20-30 instructions + 3 constants
   - Competes with other FPU operations for ROM space

5. **Testing Complexity:**
   - Must test hardware AND microcode
   - More potential failure points
   - Harder to isolate bugs

### Development Effort Estimate

**Total: 35-45 hours (4-5 days)**

| Task | Hours | Description |
|------|-------|-------------|
| **Microcode Correction Routines** | 10-12 | Write ATAN/TAN correction in microassembler |
| **CORDIC Wrapper Handoff** | 6-8 | Microcode interface, result registers |
| **FPU Core Integration** | 6-8 | Stack push, PC jump, return logic |
| **Format Converter Mods** | 4-6 | Add Q2.62 ↔ FP80 modes |
| **Exception Handling** | 4-6 | Validation, flag generation |
| **FP80 Negate** | 2-3 | Special value handling |
| **Integration & Debug** | 6-8 | Wire up, test microcode execution |
| **Verification** | 4-6 | Test correction accuracy, microcode flow |
| **TOTAL** | **42-57** | **~1 week** |

---

## Plan 4: Full Microcode Implementation

### Architecture

**Strategy:** Implement entire TAN/ATAN correction in FPU microcode, with CORDIC as a microcode subroutine.

**Key Insight:** The 8087 itself is heavily microcoded. Why not go all the way and implement TAN/ATAN entirely in microcode?

**Conceptual Flow:**
```
User calls FPTAN/FPATAN
  ↓
CPU ESC instruction → FPU microsequencer
  ↓
FPU Microcode:
  1. Range reduction (using FPU arithmetic)
  2. Call CORDIC microcode subroutine (16 iterations)
  3. Polynomial correction (FPU arithmetic)
  4. Assemble result
  5. Return to CPU
```

**Block Diagram:**
```
┌──────────────────────────────────────────────────┐
│ FPU Microsequencer                               │
├──────────────────────────────────────────────────┤
│                                                  │
│  FPTAN/FPATAN Microcode Entry Point:            │
│  ┌────────────────────────────────────────────┐ │
│  │ 1. Range Reduction                         │ │
│  │    - FP_DIV angle, π/2                     │ │
│  │    - FP_FRAC to get fractional part        │ │
│  │    - FP_MUL frac, π/2                      │ │
│  └──────────────┬─────────────────────────────┘ │
│                 │                                │
│  ┌──────────────▼─────────────────────────────┐ │
│  │ 2. CORDIC Microcode Loop (16 iterations)   │ │
│  │    FOR i = 0 TO 15:                        │ │
│  │      IF z >= 0:                            │ │
│  │        x_new = x - (y >> i)                │ │
│  │        y_new = y + (x >> i)                │ │
│  │        z_new = z - atan[i]                 │ │
│  │      ELSE:                                 │ │
│  │        x_new = x + (y >> i)                │ │
│  │        y_new = y - (x >> i)                │ │
│  │        z_new = z + atan[i]                 │ │
│  │    ENDFOR                                  │ │
│  └──────────────┬─────────────────────────────┘ │
│                 │                                │
│  ┌──────────────▼─────────────────────────────┐ │
│  │ 3. Polynomial Correction                   │ │
│  │    - FP_MUL ε, ε                           │ │
│  │    - FP_MUL ε², coeff                      │ │
│  │    - FP_ADD 1, ...                         │ │
│  │    - FP_MUL ε, ...                         │ │
│  │    - FP_ADD CORDIC_result, correction      │ │
│  └──────────────┬─────────────────────────────┘ │
│                 │                                │
│  ┌──────────────▼─────────────────────────────┐ │
│  │ 4. Return Result to FPU Stack              │ │
│  └────────────────────────────────────────────┘ │
│                                                  │
└──────────────────────────────────────────────────┘
```

### Implementation Details

#### 1. CORDIC in Microcode

**Problem:** CORDIC requires shift operations, which are not native FPU operations.

**Solutions:**

**Option A: Add microcode shift instructions**
```verilog
// New microcode instructions for CORDIC
MICROCODE_SHIFT_RIGHT_ARITH  // Arithmetic right shift (sign-extend)
MICROCODE_SHIFT_LEFT         // Logical left shift
```

**Option B: Use FPU multiply for shifts**
```assembly
# Right shift by i = multiply by 2^-i
FLD @SHIFT_TABLE[i];   # Load 2^-i constant
FMUL ST(1), ST(0);     # Multiply by 2^-i (equivalent to >> i)
```

**Recommendation:** Use Option B (multiply by powers of 2) to avoid adding new instructions.

**CORDIC Microcode Subroutine:**

**File:** `Quartus/rtl/FPU8087/microcode/cordic_microcode.us`

```assembly
# CORDIC Rotation Mode (16 iterations) - Microcode Implementation
# Input: ST(0) = z (angle), ST(1) = y (0.0), ST(2) = x (1/K ≈ 0.607)
# Output: ST(0) = sin(z), ST(1) = cos(z)
# Uses: ST(3) to ST(7) for temporaries

microcode cordic_rotation_16 {
    # Iteration counter in special register
    MOV @ITER_COUNT, 0;

cordic_loop:
    # Load iteration index
    FLD @ITER_COUNT;       # ST(0) = i

    # Compute shift amount: 2^-i
    FLD @SHIFT_TABLE;      # Load base address
    FADD ST(0), ST(1);     # Add index
    FLD [ST(0)];           # Load 2^-i → ST(0) = 2^-i, ST(1) = i, ST(2) = z, ST(3) = y, ST(4) = x
    MOV ST(7), ST(0);      # Save 2^-i to ST(7)
    FSTP ST(0);            # Pop
    FSTP ST(0);            # Pop i

    # Load x, y, z
    FLD ST(2);             # ST(0) = x
    FLD ST(2);             # ST(0) = y, ST(1) = x
    FLD ST(2);             # ST(0) = z, ST(1) = y, ST(2) = x

    # Check sign of z
    FTST;                  # Test ST(0) (z)
    FSTSW AX;              # Store status
    SAHF;                  # Load into flags
    JNS cordic_z_positive;

cordic_z_negative:
    # z < 0: x_new = x + y·2^-i, y_new = y - x·2^-i, z_new = z + atan[i]

    # Compute y·2^-i
    FLD ST(1);             # Duplicate y → ST(0) = y
    FMUL ST(7);            # Multiply by 2^-i → ST(0) = y·2^-i
    FADD ST(2), ST(0);     # x_new = x + y·2^-i (stored in ST(2))
    FSTP ST(0);            # Pop y·2^-i

    # Compute x·2^-i
    FLD ST(2);             # Duplicate x → ST(0) = x
    FMUL ST(7);            # Multiply by 2^-i → ST(0) = x·2^-i
    FSUB ST(1), ST(0);     # y_new = y - x·2^-i (stored in ST(1))
    FSTP ST(0);            # Pop x·2^-i

    # Load atan[i]
    FLD @ITER_COUNT;       # ST(0) = i
    FLD @ATAN_TABLE;       # Base address
    FADD ST(0), ST(1);     # Add index
    FLD [ST(0)];           # Load atan[i] → ST(0) = atan[i]
    FSTP ST(1);            # Remove temps
    FSTP ST(1);

    FADD ST(0), ST(0);     # z_new = z + atan[i]

    JMP cordic_update;

cordic_z_positive:
    # z >= 0: x_new = x - y·2^-i, y_new = y + x·2^-i, z_new = z - atan[i]

    # Similar to z_negative but with reversed signs
    # ... (similar code) ...

cordic_update:
    # Store updated x, y, z back
    MOV ST(2), ST(0);      # Store z
    MOV ST(3), ST(1);      # Store y
    MOV ST(4), ST(2);      # Store x

    # Increment iteration counter
    FLD @ITER_COUNT;
    FLD @FP80_ONE;
    FADD;
    MOV @ITER_COUNT, ST(0);

    # Check if done (i < 16)
    FLD @FP80_16;
    FCOM;
    FSTSW AX;
    SAHF;
    JL cordic_loop;

cordic_done:
    # Results: ST(0) = sin(z), ST(1) = cos(z)
    RET;
}
```

**Challenge:** This is **very complex** and requires:
- ~200-300 microinstructions for full CORDIC + correction
- Extensive use of FPU stack (8 registers)
- Many temporary values
- Slow (each FPU operation takes 3-6 cycles)

#### 2. Performance Estimation

**CORDIC Microcode Cycle Count (16 iterations):**
- Per iteration:
  - Load constants: 3-5 cycles
  - Multiply (2× for x·2^-i and y·2^-i): 2 × 4 = 8 cycles
  - Add/Sub (3× for x_new, y_new, z_new): 3 × 3 = 9 cycles
  - Conditionals and jumps: 2-3 cycles
  - **Total per iteration: ~22-25 cycles**
- **16 iterations: 16 × 23 = 368 cycles**

**Correction Microcode:** +20-25 cycles (same as Plan 3)

**Total: ~390-400 cycles** for TAN/ATAN

**This is SLOWER than the current 50-iteration hardware CORDIC!**

### Area Analysis

**Hardware Additions:**

| Component | ALMs | Description |
|-----------|------|-------------|
| **Microcode Interface** | +10-15 | Entry point, return handling |
| **Exception Handling** | +40-50 | Validation (still needed in hardware) |
| **Microcode ROM** | +30-40 | 200-300 microinstructions × 32 bits |
| **TOTAL** | **+80-105** | **Average: ~90 ALMs** |

**Microcode ROM:**
- CORDIC routine: ~200 microinstructions
- Correction routine: ~30 microinstructions
- Constants: 16 atan values + 3 correction coeffs = ~1.5 KB

**Percentage of Total FPU:**
- Plan 4 additions: ~90 ALMs (0.2%)
- **Lowest hardware cost of all plans**

### Pros and Cons

#### ✅ Pros

1. **Absolute Minimum Hardware:**
   - +90 ALMs (lowest of all plans)
   - Almost no new hardware modules
   - Tiny area footprint

2. **Maximum Flexibility:**
   - Entire algorithm in microcode (easy to modify)
   - Can implement complex corrections
   - Easy to add new transcendental functions

3. **Simple Hardware Interface:**
   - Just entry/exit points
   - No complex state machines
   - Minimal CORDIC wrapper changes

4. **Reuses FPU Infrastructure:**
   - Uses existing FPU stack
   - Uses existing arithmetic units
   - No new modules at all

#### ❌ Cons

1. **TERRIBLE Performance:**
   - **~390-400 cycles** for TAN/ATAN
   - **SLOWER than current 350-cycle implementation!**
   - 10× slower than Plan 1
   - Makes TAN/ATAN unusable for real applications

2. **Massive Microcode Complexity:**
   - 200-300 microinstructions
   - Very hard to write and debug
   - Stack management nightmare
   - Many temporaries needed

3. **Large Microcode ROM:**
   - ~230 microinstructions + constants
   - Competes with other FPU operations
   - May exceed available ROM space

4. **NOT Recommended:**
   - Performance is unacceptable
   - Defeats the purpose of hardware CORDIC
   - Better to just use software implementation

### Recommendation

**DO NOT IMPLEMENT PLAN 4.**

While it has the lowest hardware cost, the performance penalty is catastrophic. Full microcode implementation of CORDIC is too slow to be useful.

**Conclusion:** Keep CORDIC in hardware, use microcode only for correction (Plan 3) or use dedicated hardware (Plan 1).

---

## Plan 5: Minimal Enhancement (Quality-of-Life Improvements Only)

### Architecture

**Strategy:** Make the **minimal changes** necessary to improve quality, accuracy, and 8087 compliance **without changing the fundamental CORDIC algorithm**.

**What's Preserved:**
- Pure 50-iteration CORDIC for all operations (SIN, COS, TAN, ATAN)
- Current performance characteristics
- Simple architecture (no dual paths, no correction units)

**What's Enhanced:**
1. Proper FP80 conversion (use format converter)
2. Proper quadrant handling (IEEE-compliant negate)
3. Comprehensive exception handling (8087 flags)
4. Optional early termination (small performance boost)

**This does NOT match 8087 exactly** (still 50 iterations, no correction), but it improves accuracy and compliance.

### Implementation Details

#### 1. Proper FP80 Conversion (Same as all other plans)

```verilog
// Add MODE_FP80_TO_FIXED64 and MODE_FIXED64_TO_FP80 to format converter
// Instantiate converter instances in CORDIC wrapper
// (Same as Plans 1-3)
```

**Area Impact:** +40-50 ALMs
**Latency:** +1-2 cycles per conversion

#### 2. Proper FP80 Negate (Same as all other plans)

```verilog
function [79:0] fp80_negate;
    // Special value handling (same as Plans 1-3)
endfunction
```

**Area Impact:** +15-20 ALMs
**Latency:** 0 cycles (combinational)

#### 3. Comprehensive Exception Handling (Same as all other plans)

```verilog
// Input validation state
// Exception flag outputs
// (Same as Plans 1-3)
```

**Area Impact:** +40-50 ALMs
**Latency:** +1 cycle (validation state)

#### 4. Early Termination (Optional Performance Boost)

```verilog
// Early termination for small angles
STATE_CORDIC_ITER: begin
    // ... existing CORDIC micro-rotation ...

    // Early termination check
    reg early_terminate;
    if (cordic_mode == MODE_ROTATION) begin
        // Check if |z| < threshold
        early_terminate = (z_next < 64'h0000_0000_0000_0100) &&
                          (z_next > 64'hFFFF_FFFF_FFFF_FF00);
    end else begin
        // Check if |y| < threshold
        early_terminate = (y_next < 64'h0000_0000_0000_0100) &&
                          (y_next > 64'hFFFF_FFFF_FFFF_FF00);
    end

    // Terminate early or continue
    if (early_terminate || iteration_count >= NUM_ITERATIONS - 1) begin
        state <= STATE_CONVERT_OUTPUT;
    end else begin
        iteration_count <= iteration_count + 1;
    end
end
```

**Area Impact:** +10-15 ALMs
**Performance:** -10 to -30 cycles for small angles (average -10 cycles)

### Performance Analysis

**Cycle Counts (with early termination):**

| Operation | Current | Plan 5 (Minimal) | Plan 1 (Full HW) | 8087 |
|-----------|---------|------------------|------------------|------|
| **FSIN**  | 50-55   | 40-55 (avg 48)   | 50-55            | 200-300 |
| **FCOS**  | 50-55   | 40-55 (avg 48)   | 50-55            | 200-300 |
| **FSINCOS** | 50-55 | 40-55 (avg 48)   | 50-55            | 250-350 |
| **FPTAN** | ~350    | ~340 (avg)       | **35-40**        | 200-250 |
| **FPATAN** | ~350   | ~340 (avg)       | **35-40**        | 200-300 |

**Note:** Plan 5 does NOT achieve 8087-like performance for TAN/ATAN because it still uses 50 iterations instead of 16+correction.

**Speedup:** ~3% improvement on average (not significant)

### Area Analysis

**Hardware Additions:**

| Component | ALMs | Description |
|-----------|------|-------------|
| **Format Converter Mods** | +40-50 | MODE_FP80_TO_FIXED64, MODE_FIXED64_TO_FP80 |
| **FP80 Negate Function** | +15-20 | Special value handling logic |
| **Exception Handling** | +40-50 | Validation, flag generation |
| **Early Termination (Opt)** | +10-15 | Comparators and termination logic |
| **TOTAL** | **+105-135** | **Average: ~120 ALMs** |

**Percentage of Total FPU:**
- Plan 5 additions: ~120 ALMs (0.3%)
- **Second-lowest hardware cost (after Plan 4)**

### Pros and Cons

#### ✅ Pros

1. **Low Hardware Cost:**
   - +120 ALMs (second-lowest after Plan 4)
   - No major new modules
   - Incremental improvements only

2. **Low Risk:**
   - Minimal changes to existing design
   - No algorithmic changes
   - Easy to verify

3. **Shortest Development Time:**
   - 15-20 hours (3-4 days)
   - Straightforward implementation
   - Low testing burden

4. **Improves Quality:**
   - Proper FP80 conversions (better accuracy)
   - Exception handling (8087 compliance)
   - Special value handling (robustness)

5. **Backward Compatible:**
   - No changes to core CORDIC algorithm
   - Same performance characteristics
   - Drop-in replacement

#### ❌ Cons

1. **Does NOT Match 8087:**
   - Still uses 50 iterations (not 16)
   - No correction phase
   - Different algorithm entirely
   - **Fails primary objective**

2. **No Performance Improvement for TAN/ATAN:**
   - TAN still ~350 cycles (not 35-40)
   - ATAN still ~350 cycles (not 35-40)
   - **10× slower than 8087-accurate implementation**

3. **Misses Opportunity:**
   - Doesn't leverage 8087's hybrid approach
   - Continues inefficient pure CORDIC for TAN/ATAN
   - Doesn't achieve target accuracy (<1 ULP guaranteed)

4. **Partial Solution:**
   - Improves compliance but not core algorithm
   - Band-aid fix rather than proper enhancement
   - Will likely need revisiting later

5. **User Expectation Mismatch:**
   - Users expect 8087 behavior (16 iter + correction)
   - Plan 5 delivers different algorithm
   - May cause confusion

### Recommendation

**Plan 5 is suitable ONLY if:**
- 8087 exact match is NOT required
- Performance improvement is not a priority
- Only quality/compliance improvements are needed
- Development time is severely constrained

**Plan 5 is NOT suitable if:**
- ✅ Goal is to match 8087 behavior (as stated in requirements)
- ✅ Performance improvement is desired
- ✅ Achieving <1 ULP guaranteed accuracy is important

**For the stated objectives, Plan 5 FAILS** because it does not implement the 8087's hybrid CORDIC + correction approach.

---

## Comparison and Recommendation

### Summary Table

| Plan | Hardware (ALMs) | Cycles (TAN) | Cycles (ATAN) | 8087 Match | Dev Time (hrs) | Risk | Recommendation |
|------|-----------------|--------------|---------------|------------|----------------|------|----------------|
| **Plan 1: Full HW** | +285 | 35-40 | 35-40 | ✅ Exact | 40-50 | Medium | **Best for performance** |
| **Plan 2: Unit Reuse** | +190 | 50-70 | 50-70 | ✅ Exact | 30-40 | Low | **Best for area/effort balance** |
| **Plan 3: Hybrid HW+MC** | +175 | 45-60 | 45-60 | ✅ Exact | 35-45 | Medium | **Best for flexibility** |
| **Plan 4: Full Microcode** | +90 | 390-400 | 390-400 | ⚠️ Slow | 50-60 | High | **DO NOT USE** |
| **Plan 5: Minimal** | +120 | 340 | 340 | ❌ No | 15-20 | Low | **Fails requirements** |

### Detailed Comparison

#### Performance Winner: **Plan 1 (Full Hardware)**

- **TAN:** 35-40 cycles (10× speedup)
- **ATAN:** 35-40 cycles (10× speedup)
- **Deterministic timing** (fixed 16 iterations + correction)
- **Closest to 8087 performance**

#### Area Winner: **Plan 2 (Heavy Unit Reuse)**

- **+190 ALMs** (33% less than Plan 1)
- **Still achieves 8087 accuracy**
- **Good performance** (5-7× speedup)
- **Best hardware efficiency**

#### Flexibility Winner: **Plan 3 (Hybrid HW+Microcode)**

- **Correction in microcode** (easy to update)
- **No shared unit contention**
- **Good performance** (6-8× speedup)
- **Moderate hardware cost** (+175 ALMs)

#### DO NOT USE: **Plan 4 (Full Microcode)**

- **Performance disaster** (390-400 cycles - SLOWER than current!)
- **Massive microcode complexity**
- **No redeeming qualities**

#### Fails Requirements: **Plan 5 (Minimal)**

- **Does not match 8087** (50 iterations, no correction)
- **No performance improvement** for TAN/ATAN
- **Only suitable for quality fixes**, not algorithm enhancement

### Final Recommendation

**For your stated objective** ("make TAN ATAN exactly as 8087" with "correction and reduce iterations"):

### 🏆 **Recommended: Plan 2 (Heavy Unit Reuse)**

**Rationale:**
1. ✅ **Achieves 8087 exact match** (16 iterations + correction)
2. ✅ **Best area efficiency** (+190 ALMs, 33% savings vs Plan 1)
3. ✅ **Good performance** (5-7× speedup, acceptable for most uses)
4. ✅ **Reasonable development effort** (30-40 hours)
5. ✅ **Low risk** (reuses proven FPU modules)
6. ✅ **Preserves SIN/COS** (no changes to 50-iter path)

**Trade-off:** +15-30 cycles slower than Plan 1 due to shared unit latency, but still achieves 5-7× speedup and costs 95 ALMs less.

### 🥈 **Alternative: Plan 1 (Full Hardware)** if performance is critical

**Choose Plan 1 if:**
- Absolute best performance is required (10× speedup)
- Area cost is not a concern (+95 ALMs acceptable)
- Deterministic timing is mandatory
- Extra 10-15 hours development time is acceptable

### 🥉 **Alternative: Plan 3 (Hybrid HW+Microcode)** if flexibility is priority

**Choose Plan 3 if:**
- Want easy updateable correction algorithm
- Microcode infrastructure is well-established
- Prefer no shared unit contention
- Moderate performance (6-8× speedup) is acceptable

### ❌ **Avoid: Plans 4 and 5**

- **Plan 4:** Unacceptable performance (slower than current!)
- **Plan 5:** Fails stated objective (does not match 8087)

---

## Implementation Roadmap (Plan 2 - Recommended)

### Phase 1: Foundation (Week 1)

**Days 1-2: Format Converter Modifications**
- Add MODE_FP80_TO_FIXED64 (FP80 → Q2.62)
- Add MODE_FIXED64_TO_FP80 (Q2.62 → FP80)
- Test round-trip conversions
- **Deliverable:** Enhanced format converter with Q2.62 support

**Days 3-4: Exception Handling**
- Add input validation state
- Implement flag outputs (invalid, overflow, underflow, inexact)
- Add FP80 negate function with special value handling
- **Deliverable:** Robust exception handling

**Day 5: Dual Path Routing**
- Add mode selection (SIN/COS vs TAN/ATAN)
- Implement iteration count switching (50 vs 16)
- **Deliverable:** Dual CORDIC paths working

### Phase 2: Correction Implementation (Week 2)

**Days 6-7: Correction State Machine**
- Add 5 correction states (ε², ε²·c, 1±ε²·c, ε·(...), combine)
- Implement correction constant ROM
- Add shared unit request logic
- **Deliverable:** Correction state machine skeleton

**Days 8-9: Integration and Debugging**
- Wire up correction to CORDIC wrapper
- Connect shared unit interface
- Test CORDIC → correction → output flow
- **Deliverable:** Integrated system

**Day 10: Verification and Tuning**
- Compare against 8087 reference values
- Measure ULP error
- Test all quadrants and edge cases
- Performance profiling
- **Deliverable:** Verified, accurate implementation

### Success Criteria

1. ✅ **Accuracy:** <1 ULP error for TAN/ATAN (matches 8087)
2. ✅ **Performance:** 50-70 cycles for TAN/ATAN (5-7× speedup)
3. ✅ **Compliance:** All exception flags work correctly
4. ✅ **Preservation:** SIN/COS unchanged (50 iterations, same accuracy)
5. ✅ **Area:** +190 ALMs (within budget)

---

## Appendix A: 8087 Correction Polynomial Derivation

### ATAN Correction

For small ε (ε < 2^-16), the Taylor series for atan is:

```
atan(ε) = ε - ε³/3 + ε⁵/5 - ε⁷/7 + ...
```

For |ε| < 2^-16, higher-order terms are negligible:

```
atan(ε) ≈ ε - ε³/3
atan(ε) ≈ ε·(1 - ε²/3)
```

**Rational approximation:**
```
atan(ε) ≈ ε·(1 - 0.333333·ε²)
```

**Coefficients:**
- C₁ = 1.0 = 0x3FFF8000000000000000
- C₃ = -1/3 ≈ -0.333333... = 0xBFFDAAAAAAAAAAAA0000

### TAN Correction

For small ε, the Taylor series for tan is:

```
tan(ε) = ε + ε³/3 + 2ε⁵/15 + ...
```

For |ε| < 2^-16:

```
tan(ε) ≈ ε + ε³/3
tan(ε) ≈ ε·(1 + ε²/3)
```

**Rational approximation:**
```
tan(ε) ≈ ε·(1 + 0.333333·ε²)
```

**Coefficients:**
- C₁ = 1.0 = 0x3FFF8000000000000000
- C₃ = +1/3 ≈ +0.333333... = 0x3FFDAAAAAAAAAAA00000

### Error Analysis

After 16 CORDIC iterations, residual |ε| < 2^-16.

**ATAN:**
```
Error ≈ ε⁵/5 < (2^-16)⁵/5 ≈ 10^-24 radians ≈ 0.0001 ULP
```

**TAN:**
```
Error ≈ 2ε⁵/15 < 2·(2^-16)⁵/15 ≈ 10^-24 ≈ 0.0001 ULP
```

**Conclusion:** Third-order correction achieves <1 ULP for 64-bit mantissa.

---

## Appendix B: Area Breakdown by Module

### Plan 1 (Full Hardware): +285 ALMs

```
Correction Unit:                    +80-100 ALMs
  ├── State machine (7 states)        +20 ALMs
  ├── ROM constants (4 FP80)          +10 ALMs
  ├── Muxing logic                    +15 ALMs
  ├── Epsilon register                +10 ALMs
  ├── Intermediate result regs        +25 ALMs
  └── Control signals                 +10 ALMs

Format Converter Mods:              +40-50 ALMs
  ├── MODE_FP80_TO_FIXED64 logic      +20 ALMs
  ├── MODE_FIXED64_TO_FP80 logic      +20 ALMs
  └── Mode selection mux              +5 ALMs

FP80 Negate Function:               +15-20 ALMs
  ├── Special value checks            +10 ALMs
  └── Sign/exp/mant packing           +5 ALMs

Exception Handling:                 +40-50 ALMs
  ├── Validation state                +15 ALMs
  ├── Flag generation logic           +20 ALMs
  └── Indefinite NaN handling         +10 ALMs

Dual Path Routing:                  +20-25 ALMs
  ├── Mode selection mux              +10 ALMs
  └── Iteration count mux             +10 ALMs

Shared Unit Arbitration:            +30-40 ALMs
  ├── Request arbitration logic       +20 ALMs
  └── Response routing                +15 ALMs

Misc (ROM constants, glue):         +10-15 ALMs
```

### Plan 2 (Heavy Unit Reuse): +190 ALMs

```
Correction State Machine:           +30-40 ALMs
  ├── 5 correction states             +15 ALMs
  ├── Sequencing logic                +10 ALMs
  └── Temporary registers             +10 ALMs

Correction Constants ROM:           +10-15 ALMs
  └── 4 FP80 inline constants         +12 ALMs

Format Converter Mods:              +40-50 ALMs
  (Same as Plan 1)

FP80 Negate Function:               +15-20 ALMs
  (Same as Plan 1)

Exception Handling:                 +40-50 ALMs
  (Same as Plan 1)

Dual Path Routing:                  +20-25 ALMs
  (Same as Plan 1)

Shared Unit Interface:              +10-15 ALMs
  ├── Request/response muxing         +8 ALMs
  └── Handshake logic                 +5 ALMs

Misc:                               +5-10 ALMs
```

**Savings vs Plan 1:** No dedicated correction unit (-80 ALMs), simpler arbitration (-20 ALMs)

---

**END OF DOCUMENT**

**Files to Create:**
1. This markdown document: `CORDIC_Enhancement_Implementation_Plans.md`
2. Next steps: Choose plan, begin implementation

**Recommendation:** **Implement Plan 2 (Heavy Unit Reuse)** for best area/performance/effort balance.
