# True Multi-Precision Payne-Hanek: Requirements Analysis

**Date:** 2025-11-14
**Status:** Feasibility Study
**Goal:** Determine requirements for full-precision Payne-Hanek implementation

---

## Current Implementation (Phase 3B) - Simplified

**Algorithm:**
```
1. n = angle × (2/π)              // Single FP80 multiply
2. int_part = floor(n)             // Extract integer
3. frac = n - int_part             // Get fractional part
4. reduced = frac × (π/2)          // Scale to radians
```

**Limitations:**
- Uses only 80-bit precision (2/π as FP80)
- No multi-precision multiplication
- No bit-selection based on exponent
- Accuracy limited to ~1e-6 for large angles

**Current Resources:**
- 25 microcode instructions
- ~45 cycles execution
- Uses existing FPU AddSub and MulDiv units
- Custom FLOOR operation
- ~272 ALMs total

---

## True Multi-Precision Payne-Hanek Algorithm

### High-Level Algorithm

```
Input: angle (FP80) = sign × 2^(exp-bias) × mantissa

1. Exponent Analysis
   - Extract exponent e from angle
   - Determine bit position: k = e - bias + 63

2. Chunk Selection
   - Select which 64-bit chunks of 2/π to use
   - Typically need 2-3 chunks for 128-bit precision
   - Chunk index: i = k / 64

3. Bit Alignment
   - Align angle mantissa with selected 2/π chunks
   - Shift amount: s = k mod 64

4. Multi-Precision Multiplication
   - Multiply: mantissa × 2/π[chunks]
   - Result: 128-bit or 192-bit product

5. Integer/Fractional Extraction
   - Extract integer part → quadrant = int_part mod 4
   - Extract fractional part (64-bit precision)

6. Fraction to FP80 Conversion
   - Convert 64-bit fractional part to FP80
   - Normalize to [0, 1) range

7. Final Scaling
   - reduced = frac × (π/2)
```

**Accuracy:** <1e-15 for all practical angles

---

## Required New Units

### 1. Multi-Precision Multiplier (64×64 → 128-bit)

**Purpose:** Multiply angle mantissa by 2/π chunks

**Interface:**
```verilog
module Multi_Precision_Multiplier (
    input wire clk,
    input wire reset,
    input wire enable,
    input wire [63:0] operand_a,    // Angle mantissa
    input wire [63:0] operand_b,    // 2/π chunk
    output reg [127:0] result,      // 128-bit product
    output reg done
);
```

**Implementation Options:**

**Option A: Dedicated 64×64 Multiplier**
- Use DSP blocks if available
- Latency: 3-5 cycles
- Area: ~150-200 ALMs + DSP blocks
- Pros: Fast, pipelined
- Cons: Uses precious DSP resources

**Option B: Reuse FPU Multiplier**
- Extract mantissas, use FPU_IEEE754_MulDiv_Unified
- Reconstruct 128-bit result from FP80 output
- Latency: 6-7 cycles
- Area: 0 (reuses existing)
- Pros: No additional hardware
- Cons: Requires mantissa extraction/packing

**Recommendation:** Option B (reuse FPU multiplier)

**Estimated Area:** 0 ALMs (reuses existing)

---

### 2. Exponent Analyzer and Chunk Selector

**Purpose:** Determine which 2/π chunks to load based on angle exponent

**Interface:**
```verilog
module Chunk_Selector (
    input wire [14:0] angle_exponent,  // From FP80 angle
    output reg [1:0] chunk_index,      // Which ROM chunk (0-3)
    output reg [5:0] bit_shift,        // Bit alignment shift
    output reg [2:0] num_chunks        // How many chunks needed (1-3)
);
```

**Logic:**
```verilog
always @(*) begin
    // k = exponent - bias + 63
    integer k = angle_exponent - 15'h3FFF + 63;

    // Chunk index = k / 64
    chunk_index = k[7:6];  // Divide by 64

    // Bit shift = k mod 64
    bit_shift = k[5:0];    // Remainder

    // Number of chunks needed for precision
    num_chunks = (bit_shift > 32) ? 3 : 2;
end
```

**Estimated Area:** ~20-30 ALMs (combinational logic)

---

### 3. Bit Alignment and Shifter Unit

**Purpose:** Align angle mantissa with selected 2/π chunks

**Interface:**
```verilog
module Bit_Aligner (
    input wire [63:0] mantissa_in,
    input wire [5:0] shift_amount,
    output reg [127:0] mantissa_aligned  // Extended for alignment
);
```

**Logic:**
```verilog
always @(*) begin
    // Shift mantissa left by shift_amount
    // Zero-extend to 128 bits for multi-precision multiply
    mantissa_aligned = {mantissa_in, 64'b0} << shift_amount;
end
```

**Estimated Area:** ~40-50 ALMs (barrel shifter)

---

### 4. Multi-Precision Accumulator

**Purpose:** Accumulate results from multiple chunk multiplications

**Interface:**
```verilog
module Multi_Precision_Accumulator (
    input wire clk,
    input wire reset,
    input wire enable,
    input wire clear,
    input wire [127:0] addend,
    output reg [191:0] accumulator  // Support up to 3 chunks
);
```

**Logic:**
```verilog
always @(posedge clk or posedge reset) begin
    if (reset)
        accumulator <= 192'b0;
    else if (clear)
        accumulator <= 192'b0;
    else if (enable)
        accumulator <= accumulator + {{64{1'b0}}, addend};
end
```

**Estimated Area:** ~80-100 ALMs (192-bit adder + register)

---

### 5. Integer/Fractional Extractor

**Purpose:** Extract integer and fractional parts from multi-precision result

**Interface:**
```verilog
module Int_Frac_Extractor (
    input wire [191:0] product,          // From accumulator
    input wire [5:0] bit_position,       // Where integer/frac boundary is
    output reg [7:0] integer_part,       // For quadrant (only need 8 bits)
    output reg [63:0] fractional_part    // Fractional part
);
```

**Logic:**
```verilog
always @(*) begin
    // Extract bits based on bit_position
    // Integer part: bits [bit_position+63 : bit_position]
    // Fractional part: bits [bit_position-1 : bit_position-64]

    integer_part = product[bit_position +: 8];
    fractional_part = product[(bit_position-64) +: 64];
end
```

**Estimated Area:** ~30-40 ALMs (bit selection logic)

---

### 6. Fractional to FP80 Converter

**Purpose:** Convert 64-bit fractional integer to FP80 in range [0, 1)

**Interface:**
```verilog
module Frac_To_FP80 (
    input wire [63:0] fractional_bits,
    output reg [79:0] fp80_result
);
```

**Logic:**
```verilog
always @(*) begin
    // Find leading 1 in fractional_bits
    // Normalize and set exponent accordingly

    if (fractional_bits == 0) begin
        fp80_result = 80'b0;
    end else begin
        // Find position of leading 1
        integer leading_one_pos;
        // ... leading zero count logic ...

        // Normalize mantissa
        reg [63:0] normalized = fractional_bits << (63 - leading_one_pos);

        // Set exponent for range [0.5, 1.0)
        // Exponent = 0x3FFE - (63 - leading_one_pos)
        reg [14:0] exponent = 15'h3FFE - (63 - leading_one_pos);

        // Pack FP80
        fp80_result = {1'b0, exponent, normalized};
    end
end
```

**Estimated Area:** ~60-80 ALMs (leading zero counter + normalization)

---

## Modifications to Existing Units

### 1. Microsequencer_Extended_BCD.v

**Current:** 25 instructions for simplified algorithm

**Needed for Multi-Precision:**

**New Micro-Operations:**
```verilog
// Exponent and chunk selection
localparam MOP_EXTRACT_EXP     = 5'd26;  // Extract exponent from FP80
localparam MOP_SELECT_CHUNKS   = 5'd27;  // Determine chunk selection
localparam MOP_ALIGN_MANTISSA  = 5'd28;  // Bit-align mantissa

// Multi-precision operations
localparam MOP_CLEAR_ACCUM_192 = 5'd29;  // Clear 192-bit accumulator
localparam MOP_MUL_ACCUM       = 5'd30;  // Multiply and accumulate
localparam MOP_EXTRACT_INT_FRAC = 5'd31; // Extract integer/fractional parts

// Conversion operations
localparam MOP_FRAC_TO_FP80    = 5'd16;  // Convert fraction to FP80
localparam MOP_MOD4            = 5'd17;  // Extract quadrant (int_part mod 4)
```

**New Microcode Sequence (Estimated 50-60 instructions):**
```
Program 22 (Multi-Precision Payne-Hanek):
Address: 0x0180-0x01C0 (64 instruction slots)

Step 1: Exponent Analysis (5 instructions)
  - Load angle
  - Extract exponent
  - Determine chunk index and shift amount

Step 2: First Chunk Multiply (10 instructions)
  - Load ROM chunk[i]
  - Extract and align mantissa
  - Multiply (using FPU or dedicated multiplier)
  - Store in accumulator

Step 3: Second Chunk Multiply (10 instructions)
  - Load ROM chunk[i+1]
  - Shift appropriately
  - Multiply
  - Accumulate

Step 4: Third Chunk Multiply (optional, 10 instructions)
  - Load ROM chunk[i+2]
  - Multiply and accumulate

Step 5: Extract Integer/Fractional Parts (8 instructions)
  - Extract integer part
  - Calculate quadrant (mod 4)
  - Extract fractional part (64-bit)

Step 6: Convert Fraction to FP80 (5 instructions)
  - Normalize fractional part
  - Pack as FP80 in range [0, 1)

Step 7: Final Scaling (7 instructions)
  - Load π/2 from ROM
  - Multiply frac × (π/2)
  - Return result

Total: ~55 instructions
```

**Estimated Area Impact:** +30 microcode instructions × 32 bits = +960 bits ≈ negligible

---

### 2. FPU_Payne_Hanek_ROM.v

**Current:** 6 ROM addresses (0-5)
- 0-3: 2/π chunks (64-bit each, zero-extended to 80-bit)
- 4: π/2 (FP80)
- 5: 2/π (FP80)

**Needed:** No changes required! ROM already has all 4 chunks of 256-bit 2/π.

**Note:** Addresses 0-3 currently zero-extend 64-bit values to 80-bit. For multi-precision, we'd extract just the lower 64 bits.

**Estimated Area Impact:** 0 ALMs (no changes)

---

### 3. Temporary Registers

**Current Registers:**
```verilog
reg [79:0] temp_fp_a;       // Operand A
reg [79:0] temp_fp_b;       // Operand B
reg [79:0] temp_fp_c;       // Scratch
reg [63:0] accum_hi;        // 64-bit accumulator high
reg [63:0] accum_lo;        // 64-bit accumulator low
```

**Additional Registers Needed:**
```verilog
// For multi-precision accumulation
reg [191:0] accum_192;      // 192-bit accumulator (3 chunks)

// For intermediate results
reg [63:0] chunk_buffer;    // Temporary chunk storage
reg [5:0] shift_amount;     // Bit alignment shift
reg [2:0] chunk_count;      // Loop counter
reg [7:0] int_part_buffer;  // Integer part for quadrant
```

**Estimated Area Impact:** ~100 ALMs (additional registers)

---

## Execution Flow Comparison

### Current (Simplified - Phase 3B)

```
Cycles: ~45-48 total

1. Load angle                    1 cycle
2. Load 2/π (FP80) from ROM      2 cycles
3. Multiply: angle × (2/π)       6 cycles (FPU)
4. FLOOR(result)                 1 cycle
5. Subtract: n - floor(n)        7 cycles (FPU)
6. Load π/2 from ROM             2 cycles
7. Multiply: frac × (π/2)        6 cycles (FPU)
8. Register moves                ~15 cycles
Total:                          ~45 cycles
```

### Multi-Precision (Proposed)

```
Cycles: ~95-110 total

1. Exponent analysis             3 cycles
2. Chunk selection               2 cycles
3. First chunk multiply          8 cycles
4. Second chunk multiply         8 cycles
5. Third chunk multiply          8 cycles (optional)
6. Accumulation                  3 cycles
7. Extract integer/fractional    5 cycles
8. Normalize fractional part     10 cycles
9. Convert to FP80               5 cycles
10. Load π/2 from ROM            2 cycles
11. Multiply: frac × (π/2)       6 cycles
12. Register moves/overhead      ~45 cycles
Total:                          ~105 cycles
```

**Performance Impact:** ~2.3× slower (105 vs 45 cycles)

---

## Area Breakdown

### New Units

| Unit | Estimated Area | Notes |
|------|----------------|-------|
| Multi-Precision Multiplier | 0 ALMs | Reuse FPU multiplier |
| Chunk Selector | 20-30 ALMs | Combinational logic |
| Bit Aligner | 40-50 ALMs | Barrel shifter |
| Multi-Precision Accumulator | 80-100 ALMs | 192-bit adder + reg |
| Int/Frac Extractor | 30-40 ALMs | Bit selection |
| Frac to FP80 Converter | 60-80 ALMs | Leading zero + norm |
| Additional Registers | 100 ALMs | 192-bit accum, etc. |
| **Total New Units** | **330-400 ALMs** | |

### Microcode Changes

| Component | Impact | Area |
|-----------|--------|------|
| Microcode ROM | +30 instructions | Negligible |
| New MOPs (8 new) | Control logic | ~40 ALMs |
| **Total Microcode** | | **~40 ALMs** |

### Total Multi-Precision Addition

**Total Added:** ~370-440 ALMs

**Current Total (Phase 3B):** ~272 ALMs
**With Multi-Precision:** ~642-712 ALMs

**Percentage of Cyclone V:** ~1.5-1.7% FPGA utilization

---

## Complexity Analysis

### Development Effort

| Task | Estimated Time | Complexity |
|------|----------------|------------|
| Design multi-precision multiplier | 4-6 hours | Medium |
| Implement chunk selector | 2-3 hours | Low |
| Create bit aligner | 3-4 hours | Medium |
| Build 192-bit accumulator | 2-3 hours | Low |
| Int/frac extractor | 3-4 hours | Medium |
| Frac to FP80 converter | 4-6 hours | High |
| Microcode sequence design | 6-8 hours | High |
| Integration and testing | 8-12 hours | High |
| **Total** | **32-46 hours** | **4-6 days** |

### Testing Requirements

1. **Unit tests** for each new module (8-12 hours)
2. **Integration tests** with microsequencer (4-6 hours)
3. **Accuracy validation** with IEEE 754 test vectors (6-8 hours)
4. **Edge case testing** (zero, infinity, very large angles) (4-6 hours)

**Total testing:** 22-32 hours (3-4 days)

**Overall project:** 54-78 hours (7-10 days)

---

## Alternative Approaches

### Option A: Hybrid Precision

**Idea:** Use multi-precision only for very large angles

```
if (angle < threshold)
    Use simplified Payne-Hanek (current, 45 cycles)
else
    Use multi-precision (105 cycles)
```

**Pros:**
- Best of both worlds
- Fast for common cases
- Accurate for extreme cases

**Cons:**
- More complex dispatch logic
- Two code paths to maintain

**Recommended threshold:** angle > 2^20 (≈1 million radians)

---

### Option B: Partial Multi-Precision

**Idea:** Use 2 chunks instead of 3

**Algorithm:**
```
- Use chunks[i] and chunks[i+1]
- 128-bit precision instead of 192-bit
- Accuracy: ~1e-12 instead of 1e-15
```

**Pros:**
- Simpler (no third multiply)
- Faster (~90 cycles vs 105)
- Less area (~300 ALMs vs 400)

**Cons:**
- Slightly less precision

**Recommended:** Good compromise for most applications

---

### Option C: Software-Assisted

**Idea:** Detect very large angles, trap to software

**Algorithm:**
```
if (angle > extreme_threshold)
    Raise exception → software handles
else
    Use hardware Payne-Hanek
```

**Pros:**
- Minimal hardware complexity
- Ultimate flexibility in software

**Cons:**
- Software trap overhead (100s of cycles)
- Only for extremely rare cases

---

## Recommendations

### For Production

**Recommended Approach:** **Option A (Hybrid Precision)**

**Implementation:**
1. Keep current simplified Payne-Hanek for angles < 2^20
2. Add multi-precision path for angles ≥ 2^20
3. Dispatch based on exponent threshold

**Rationale:**
- 99.9% of angles are < 2^20 (handled by fast path)
- Extreme angles get full precision
- Reasonable area cost (~450 ALMs total)
- Balanced performance (45 cycles typical, 105 worst-case)

**Alternative:** **Option B (Partial Multi-Precision)**

If area is critical:
- Use 2-chunk multi-precision (128-bit)
- Accuracy: ~1e-12 (vs 1e-15 for 3-chunk)
- Area: ~300 ALMs additional
- Performance: ~90 cycles

---

## Summary

### True Multi-Precision Payne-Hanek Requirements

**New Units Needed:**
1. ~~Multi-Precision Multiplier~~ (REUSE FPU multiplier) - 0 ALMs
2. Chunk Selector - 20-30 ALMs
3. Bit Aligner (barrel shifter) - 40-50 ALMs
4. 192-bit Accumulator - 80-100 ALMs
5. Integer/Fractional Extractor - 30-40 ALMs
6. Fraction to FP80 Converter - 60-80 ALMs

**Microcode Changes:**
- +30 microcode instructions
- +8 new micro-operations
- +40 ALMs control logic

**Additional Registers:**
- 192-bit accumulator
- Chunk buffers and counters
- +100 ALMs

**Total Additional Area:** ~370-440 ALMs
**Total Project Area:** ~642-712 ALMs (1.5-1.7% FPGA)

**Performance:**
- Simplified (current): ~45 cycles, ~1e-6 accuracy
- Multi-Precision (full): ~105 cycles, ~1e-15 accuracy
- Hybrid: ~45/105 cycles (threshold-based)

**Development Effort:** 7-10 days
**Testing Effort:** 3-4 days
**Total:** 10-14 days

**Recommendation:** Implement Hybrid Precision (Option A) for production use.

---

**END OF ANALYSIS**
