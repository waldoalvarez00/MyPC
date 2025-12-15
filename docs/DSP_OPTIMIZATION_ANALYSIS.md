
Analysis of synthesis usage log

Top LAB consumers and viable optimizations that preserve functionality:

  - FPU_ArithmeticUnit (~37k ALUTs)
      - Move all large multiplies into DSPs. The unified mul/div already has a DSP hint; use altera_mult_add with DSP adder chain and pipeline
        the 128-bit product to keep the sum in DSP fabric.
		
      - Collapse duplicated logic across ops: if add/sub and compare share alignment/normalization, refactor into shared modules with op selects.
      - Enable retiming/physical synthesis on this hierarchy and register wide combinational cones (e.g., sign/exponent/mantissa align) to
        improve packing.
		
		
		
  - FPU_Transcendental (~24.5k) & CORDIC_Wrapper (~24k) & Range_Reduction (~18k)
  
      - Horner polynomials: enforce DSP use on each multiply; keep coefficients in MLAB ROMs; use a single adder/multiplier pipeline with staging
        to avoid parallel redundant hardware.
		
		
		
      - CORDIC: make shift tables ROM-based; share/add pipeline between sin/cos iterations if latency allows; remove unused intermediate
        precision bits if margins are generous.
		
		
		
  - FPU_IEEE754_MulDiv_Unified (~7k)
      - Force DSP for mantissa multiply (as above), and for the divider’s multiply-by-reciprocal steps if present.
      - Use small MLABs for quotient digit tables / SRT selection; add one pipeline stage on the SRT add/sub datapath for better ALM packing.
	  
  - FPU_Format_Converter_Unified (~2.7k) / AddSub (~2.3k)
      - Push constants into ROM (MLAB), use DSP for the main multiply, and serialize lesser multiplications through the same DSP if timing
        allows.
		
  - CPU Core (~2.7k) / ALU (~0.75k)
      - Force small multiplies to DSPs (multstyle="DSP" or QSF instance assignments).
      - Ensure all filter multiplies are DSPs; place coefficients in MLAB; consider lowering internal precision if margins permit.
	  





# DSP Block Optimization Analysis for MiSTer MyPC

**Date:** 2025-11-16
**Target Platform:** Intel Cyclone V 5CSEBA6U23I7 (MiSTer DE10-Nano)
**Current FPGA Utilization:** ~78% ALMs
**Available DSP Blocks:** 112 (18x18 multipliers)

## Executive Summary

This analysis identifies arithmetic operations in the MyPC codebase that can be optimized to use dedicated DSP blocks instead of logic fabric. Moving multiplications and multiply-accumulate operations to DSP blocks can:
- **Reduce ALM usage by 15-30%** for arithmetic-heavy modules
- **Improve timing closure** (DSP blocks are faster than LUT-based multipliers)
- **Lower power consumption** (dedicated blocks are more efficient)
- **Free up logic for additional features**

## Current DSP Usage Status

**Finding:** The codebase has **NO explicit DSP block inference attributes** configured.


## Priority 1: FPU Multiplication (HIGHEST IMPACT ADDED Explicit)

Already inferred as DSP


### Location
`Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v:250`


### Analysis
- **Operation:** 64-bit × 64-bit unsigned multiplication
- **Output:** 128-bit product
- **Frequency:** Every FPU multiply operation (FMUL, FIMUL, etc.)
- **Current implementation:** Single-cycle combinatorial multiplication

### Optimization Strategy

**Option A: Automatic DSP Inference (RECOMMENDED)**

Add synthesis attributes to force DSP block usage:

```verilog
(* multstyle = "dsp" *) reg [127:0] product;

// Or for entire module:
(* multstyle = "dsp" *) module FPU_IEEE754_MulDiv_Unified(
    ...
);
```

**Option B: Pipeline with DSP Blocks**

For better timing, pipeline the multiplication:

```verilog
// Stage 1: Register inputs
reg [63:0] mant_a_reg, mant_b_reg;
(* multstyle = "dsp" *) reg [127:0] product_stage1;
reg [127:0] product;

always @(posedge clk) begin
    // Pipeline stage 1
    mant_a_reg <= mant_a;
    mant_b_reg <= mant_b;
    product_stage1 <= mant_a_reg * mant_b_reg;

    // Pipeline stage 2
    product <= product_stage1;
end
```

**Option C: Booth Multiplier with DSP Blocks**

For maximum efficiency, decompose into 18x18 DSP blocks (Cyclone V native size):

```verilog
// 64-bit × 64-bit = sum of (18×18) DSP blocks
// Requires 4×4 = 16 DSP blocks for 64×64
// Cyclone V has 112 DSP blocks available

// Partition operands into 18-bit chunks
wire [17:0] a0 = mant_a[17:0];
wire [17:0] a1 = mant_a[35:18];
wire [17:0] a2 = mant_a[53:36];
wire [10:0] a3 = mant_a[63:54];  // 11 bits

wire [17:0] b0 = mant_b[17:0];
wire [17:0] b1 = mant_b[35:18];
wire [17:0] b2 = mant_b[53:36];
wire [10:0] b3 = mant_b[63:54];  // 11 bits

// Instantiate Altera/Intel DSP megafunctions
// (auto-inferred by Quartus when properly attributed)
(* multstyle = "dsp" *) wire [35:0] p00 = a0 * b0;
(* multstyle = "dsp" *) wire [35:0] p01 = a0 * b1;
(* multstyle = "dsp" *) wire [35:0] p02 = a0 * b2;
(* multstyle = "dsp" *) wire [28:0] p03 = a0 * b3;

(* multstyle = "dsp" *) wire [35:0] p10 = a1 * b0;
(* multstyle = "dsp" *) wire [35:0] p11 = a1 * b1;
(* multstyle = "dsp" *) wire [35:0] p12 = a1 * b2;
(* multstyle = "dsp" *) wire [28:0] p13 = a1 * b3;

// ... (continue for p2x, p3x)

// Sum with appropriate shifts
assign product = p00 +
                 (p01 << 18) + (p10 << 18) +
                 (p02 << 36) + (p11 << 36) + (p20 << 36) +
                 // ... etc
```




### Performance Impact
- **Timing:** DSP blocks run at 400+ MHz on Cyclone V (vs 50 MHz target) → **excellent timing margin**
- **Latency:** Same (1 cycle) or +1 cycle if pipelined (still acceptable for FPU)

---

## Priority 2: CPU ALU Multiplication

### Location
`Quartus/rtl/CPU/alu/mul.sv:33-35`

### Current Implementation
```verilog
if (is_signed)
    out[31:0] = {{16{a[15]}}, a} * {{16{b[15]}}, b};
else
    out[31:0] = {16'b0, a} * {16'b0, b};
```

Status: Already inferred as 

### Analysis
- **Operation:** 16-bit × 16-bit signed/unsigned multiplication
- **Output:** 32-bit product
- **Frequency:** Every MUL/IMUL CPU instruction
- **Critical path:** Part of combinatorial ALU

### Optimization Strategy

**Recommended Approach:**

```verilog
(* multstyle = "dsp" *) task do_mul;
    output [31:0] out;
    input is_8_bit;
    input [15:0] a;
    input [15:0] b;
    input [15:0] flags_in;
    output [15:0] flags_out;
    input is_signed;

    (* multstyle = "dsp" *) reg [31:0] mul_result;

    begin
        flags_out = flags_in;
        flags_out[ZF_IDX] = 1'b0;
        out = 32'b0;
        if (!is_8_bit) begin
            if (is_signed)
                mul_result = {{16{a[15]}}, a} * {{16{b[15]}}, b};
            else
                mul_result = {16'b0, a} * {16'b0, b};
            out[31:0] = mul_result;
            flags_out[CF_IDX] = |mul_result[31:16];
            flags_out[OF_IDX] = |mul_result[31:16];
        end else begin
            if (is_signed)
                mul_result = {16'b0, {{8{a[7]}}, a[7:0]} * {{8{b[7]}}, b[7:0]}};
            else
                mul_result = {16'b0, {8'b0, a[7:0]} * {8'b0, b[7:0]}};
            out = mul_result;
            flags_out[CF_IDX] = |mul_result[15:8];
            flags_out[OF_IDX] = |mul_result[15:8];
        end
    end
endtask
```

### Expected Resource Savings
- **Current (estimated):** ~150-250 ALMs for 16×16 multiplier
- **With DSP blocks:** 1 DSP block + ~50 ALMs
- **Savings:** ~100-200 ALMs (**0.3-0.5% FPGA reduction**)

### Performance Impact
- **Timing:** Improved (DSP blocks are faster)
- **Latency:** Same (1 cycle combinatorial)

---

## Priority 3: Video Subsystem Address Calculations

### Location
`Quartus/rtl/VGA/FBPrefetch.sv:128,132`

### Current Implementation
```verilog
// Line 128
({6'b0, graphics_row[11:1]} * 16'd40)

// Line 132
{7'b0, row_base[9:1]} * 16'd160
```

### Analysis
- **Operations:**
  - 11-bit × 6-bit constant multiplication (×40)
  - 9-bit × 8-bit constant multiplication (×160)
- **Frequency:** Every video address calculation (100+ MHz pixel clock domain)
- **Type:** Constant coefficient multipliers

### Optimization Strategy

**Option A: Shift-Add Optimization (RECOMMENDED for constants)**

Constants like 40 and 160 can be implemented efficiently with shifts:

```verilog
// 40 = 32 + 8 = (x << 5) + (x << 3)
wire [15:0] mult_40 = ({6'b0, graphics_row[11:1]} << 5) +
                      ({6'b0, graphics_row[11:1]} << 3);

// 160 = 128 + 32 = (x << 7) + (x << 5)
wire [15:0] mult_160 = ({7'b0, row_base[9:1]} << 7) +
                       ({7'b0, row_base[9:1]} << 5);
```

**Benefits:**
- No DSP blocks needed
- Minimal ALM usage (~20 ALMs per operation)
- Faster than multiplication
- Better for constant coefficients

**Option B: DSP Blocks (if needed for timing)**

```verilog
(* multstyle = "dsp" *) wire [15:0] addr_mult1 = {6'b0, graphics_row[11:1]} * 16'd40;
(* multstyle = "dsp" *) wire [15:0] addr_mult2 = {7'b0, row_base[9:1]} * 16'd160;
```

### Expected Resource Savings
- **Option A (shift-add):** Saves ~50-100 ALMs vs current implementation
- **Option B (DSP):** Uses 2 DSP blocks, saves ~30-50 ALMs

**Recommendation:** Use **Option A (shift-add)** — more efficient for small constant multipliers.

---

## Priority 4: CPU Divider Unit

### Location
`Quartus/rtl/CPU/Divider.sv`

### Current Implementation
- **Algorithm:** Non-restoring division (iterative)
- **Resources:** Pure state machine logic
- **Latency:** 16-32 cycles

### Analysis
Division is inherently iterative and does NOT benefit from DSP blocks on Cyclone V. The current implementation is optimal.

**No optimization recommended.**

---

## Implementation Recommendations

### Phase 1: Quick Wins (Low Risk, High Impact)

**1. Add Global DSP Inference Setting**

Edit `Quartus/mycore.qsf`:

```tcl
# DSP Block Optimization Settings
# Prioritize DSP blocks for multipliers over logic fabric
set_global_assignment -name DSP_BLOCK_BALANCING "DSP Blocks"
```

**Impact:** Quartus will prioritize DSP blocks over logic fabric for multiplication operations.

**2. Add Explicit Attributes to FPU Multiplier**

File: `Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v`

```verilog
// Line 85 (add attribute)
(* multstyle = "dsp" *) reg [127:0] product;
```

**Impact:** Forces DSP inference for critical 64×64 multiplier (~600-1000 ALM savings).

**3. Add Explicit Attributes to CPU ALU Multiplier**

File: `Quartus/rtl/CPU/alu/mul.sv`

```verilog
// Line 18 (add attribute)
(* multstyle = "dsp" *) task do_mul;
```

**Impact:** Forces DSP inference for CPU MUL/IMUL (~100-200 ALM savings).

### Phase 2: Advanced Optimizations (Requires Testing)

**4. Optimize Video Address Calculations with Shift-Add**

File: `Quartus/rtl/VGA/FBPrefetch.sv`

Replace constant multiplications with shift-add trees (see Priority 3 above).

**Impact:** ~50-100 ALM savings, improved timing.

**5. Pipeline FPU Multiplier (if timing issues arise)**

Add 2-stage pipeline to FPU multiplier for better timing closure at higher clock speeds.

**Impact:** +1 cycle latency, significantly improved Fmax potential.

---

## Expected Total Resource Savings

| Optimization | ALM Savings | DSP Blocks Used | Risk |
|--------------|-------------|-----------------|------|
| Global DSP setting | ~200-400 | +8-12 | Low |
| FPU 64×64 multiplier | ~600-1000 | +16 | Low |
| CPU 16×16 multiplier | ~100-200 | +1 | Low |
| Video shift-add opt | ~50-100 | 0 | Medium |
| **TOTAL** | **~950-1700** | **+17-29** | |

**Total FPGA Impact:**
- **ALM reduction:** 3-5% (out of 78% current usage)
- **DSP utilization:** 17-29 blocks out of 112 available (15-26%)
- **New FPGA utilization:** ~73-75% ALMs (healthy margin for future features)

---

## Testing Strategy

### 1. Pre-Implementation Testing
```bash
# Run full test suite before changes
cd modelsim/
./run_all_tests.sh
```

### 2. Post-Implementation Testing
```bash
# Verify functionality after DSP optimizations
./run_all_tests.sh

# Run FPU-specific tests
cd ../Quartus/rtl/FPU8087/
./run_all_tests.sh
```

### 3. FPGA Synthesis Verification
```bash
cd /home/user/MyPC/Quartus/
quartus_sh --flow compile mycore

# Check resource utilization report
quartus_sta mycore --report_level standard
```

**Critical checks:**
- ALM usage decreased
- DSP block usage increased
- Timing still meets 50 MHz (Fmax should improve)
- All functional tests pass

### 4. Hardware Validation
Test on actual MiSTer hardware to verify:
- FPU calculations remain accurate (165/165 tests must still pass)
- CPU integer multiplication works correctly
- Video modes display properly
- No timing violations or glitches

---

## Risk Assessment

### Low Risk Items
✅ **Global DSP inference setting** — Quartus handles automatically, reversible
✅ **FPU multiplier DSP attribute** — Well-defined 64×64 operation
✅ **CPU ALU multiplier DSP attribute** — Standard 16×16 operation

### Medium Risk Items
⚠️ **Video shift-add optimization** — Requires careful verification of address calculations
⚠️ **FPU pipeline modification** — Changes latency, impacts state machine timing

### Mitigation
- **Incremental implementation:** One optimization at a time
- **Regression testing:** Run full test suite after each change
- **Git branching:** Commit each optimization separately for easy rollback
- **Hardware validation:** Test on real MiSTer before merging

---

## Implementation Checklist

### Immediate Actions (Phase 1)
- [ ] Add global DSP settings to `mycore.qsf`
- [ ] Add `(* multstyle = "dsp" *)` to FPU multiplier (line 85)
- [ ] Add `(* multstyle = "dsp" *)` to CPU multiplier (line 18)
- [ ] Run synthesis and verify DSP block usage increased
- [ ] Run full regression test suite (194 tests)
- [ ] Verify timing closure at 50 MHz
- [ ] Test on MiSTer hardware
- [ ] Document results in `docs/DSP_OPTIMIZATION_RESULTS.md`

### Future Enhancements (Phase 2)
- [ ] Implement shift-add for video address calculations
- [ ] Consider FPU multiplier pipelining if Fmax target increases
- [ ] Profile DSP block availability for future features

---

## Conclusion

The MiSTer MyPC project has **significant opportunities** for DSP block optimization, particularly in:

1. **FPU 64×64 multiplication** (highest impact)
2. **CPU 16×16 multiplication** (medium impact)
3. **Video address calculations** (low impact, best with shift-add)

**Recommended immediate action:** Implement Phase 1 optimizations (global DSP setting + explicit attributes) to achieve **3-5% ALM reduction** with minimal risk and maximum benefit.

The Cyclone V has 112 DSP blocks available, and we're currently using **near-zero** — this is a major untapped resource that can free up logic for future enhancements while improving timing and power efficiency.

---

## References

- Intel Cyclone V Device Handbook (DSP Block Architecture)
- Quartus Prime User Guide: Design Recommendations (DSP Inference)
- `docs/FPU_*.md` — FPU implementation documentation
- `docs/CPU_ARCHITECTURE_BOTTLENECK_ANALYSIS.md` — Performance analysis
- `Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v` — FPU multiplier source
- `Quartus/rtl/CPU/alu/mul.sv` — CPU multiplier source
