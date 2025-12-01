# Formal Verification Refactoring Analysis
## 6 Remaining ERROR Tests

---

## **CATEGORY 1: DCache2Way Multiple Driver Issues (4 tests)**

### Tests Affected:
- DCache2Way
- DCache2Way_MemArbiter
- DCache2Way_loose
- DCache2Way_tight

### Root Cause:
**Multiple Always Blocks Assigning to Same Signals**

The following signals have conflicting drivers:
- `wbuf_valid[7:0]` - Assigned in multiple always blocks
- `just_finished_wbuf` - Assigned in multiple always blocks
- `eviction_started` - Assigned in multiple always blocks

### Error Message:
```
ERROR: Found multiple drivers for \wbuf_valid [0].
Warning: multiple conflicting drivers for $paramod\DCache2Way\...\wbuf_valid [0]:
  port Y[0] of cell $auto$async2sync.cc:238:execute$6536 ($mux)
  port Q[0] of cell $procdff$5967 ($anyinit)
```

### Problem Locations in DCache2Way.sv:
```systemverilog
// Multiple always blocks assigning to same signals:

always_ff @(posedge clk) begin
    if (reset) begin
        wbuf_valid <= 8'b0;           // Line 663
        just_finished_wbuf <= 1'b0;   // Line 667
    end
    // ... other logic
    if (some_condition)
        wbuf_valid[c_addr[3:1]] <= 1'b1;  // Line 697
end

always_ff @(posedge clk) begin  // DIFFERENT BLOCK!
    if (reset) begin
        eviction_started <= 1'b0;      // Line 785
    end
    // ... state machine logic
    just_finished_wbuf <= 1'b0;        // Line 822 - CONFLICT!
    if (wbuf_active && (|wbuf_valid)) begin
        wbuf_valid <= 8'b0;            // Line 855 - CONFLICT!
        just_finished_wbuf <= 1'b1;    // Line 857 - CONFLICT!
    end
end
```

### Refactoring Required:

#### Option 1: Consolidate into Single Always Block (PREFERRED)
Merge all assignments to these signals into one always_ff block:

```systemverilog
// REFACTORED: Single always block for write buffer control
always_ff @(posedge clk) begin
    if (reset) begin
        wbuf_valid <= 8'b0;
        just_finished_wbuf <= 1'b0;
        eviction_started <= 1'b0;
    end else begin
        // Default assignments
        just_finished_wbuf <= 1'b0;

        // Write buffer logic (priority encoded)
        if (fill_complete_condition) begin
            wbuf_valid <= 8'b0;
            just_finished_wbuf <= 1'b1;
        end else if (new_write_condition) begin
            wbuf_valid[c_addr[3:1]] <= 1'b1;
        end

        // Eviction logic
        if (new_access_condition)
            eviction_started <= 1'b0;
        else if (start_eviction_condition)
            eviction_started <= 1'b1;
    end
end
```

#### Option 2: Use Intermediate Wires
Create intermediate combinational signals and have only one always block assign:

```systemverilog
// Combinational control signals
wire clear_wbuf = fill_complete_condition;
wire set_wbuf_bit = new_write_condition;
wire [2:0] wbuf_set_idx = c_addr[3:1];

// Single sequential assignment block
always_ff @(posedge clk) begin
    if (reset)
        wbuf_valid <= 8'b0;
    else if (clear_wbuf)
        wbuf_valid <= 8'b0;
    else if (set_wbuf_bit)
        wbuf_valid[wbuf_set_idx] <= 1'b1;
end
```

### Mockup Solution:

**Verdict: Mockup is IMPRACTICAL** - The cache logic is too complex to accurately replicate.

**Best approach**: Fix the DUT by consolidating always blocks (Option 1).

**Effort**: Medium (2-4 hours to refactor and test)

---

## **CATEGORY 2: FPU_Range_Reduction Function Issue (1 test)**

### Root Cause:
**Verilog Function Called with Non-Constant Arguments**

The `fp_sub` function performs complex floating-point subtraction with loops and conditional logic that Yosys formal cannot synthesize.

### Error Message:
```
ERROR: Function \fp_sub can only be called with constant arguments.
```

### Refactoring Required:

#### Option 1: Replace with Instantiated Module
Convert the function to a proper module with state machine.

#### Option 2: Use Existing FPU_IEEE754_AddSub Module (PREFERRED)
The project already has `FPU_IEEE754_AddSub.v` - use it instead:

```systemverilog
// In FPU_Range_Reduction.v - replace fp_sub() calls

// OLD:
reduced_angle = fp_sub(angle_in, TWO_PI);

// NEW:
FPU_IEEE754_AddSub subtractor (
    .clk(clk),
    .reset(reset),
    .enable(sub_enable),
    .operand_a(angle_in),
    .operand_b(TWO_PI),
    .subtract(1'b1),
    .result(reduced_angle),
    .done(sub_done),
    // ... flags
);
```

### Mockup Solution:

**Verdict: Mockup is VIABLE** for formal verification testing (loses some accuracy).

Create a simplified stub function or use symbolic values for formal-only builds.

**Effort**:
- Mockup: Low (1 hour - just stub the function)
- Production: Medium (4-6 hours - refactor to use FPU_IEEE754_AddSub)

---

## **CATEGORY 3: FPU_Polynomial_Evaluator ROM Issue (1 test)**

### Root Cause:
**Non-Constant Memory Write Enable During Initialization**

The coefficient ROM has dynamic write enable signals that Yosys can't handle for formal verification.

### Error Message:
```
ERROR: Non-constant enable $memwr$\coeff_rom$FPU_Poly_Coeff_ROM.v:28$154_EN
       in memory initialization $meminit$\coeff_rom$FPU_Poly_Coeff_ROM.v:28$188.
```

### Refactoring Required:

#### Option 1: Convert to Pure ROM (PREFERRED)
Remove write logic, make it a true read-only memory using case statements.

#### Option 2: Initialize with $readmemh
Use Verilog's built-in memory initialization from hex file.

### Mockup Solution:

**Verdict: Mockup is IDEAL** - ROM data doesn't affect state machine properties being verified.

Create a formal-only stub ROM that returns symbolic values:

```systemverilog
// FPU_Poly_Coeff_ROM_Formal.sv
module FPU_Poly_Coeff_ROM_Formal (
    input  logic [3:0]  poly_select,
    input  logic [3:0]  coeff_index,
    output logic [79:0] coeff_out
);
    // For formal: return symbolic values
    (* anyconst *) logic [79:0] coeff_data [0:127];

    assign coeff_out = coeff_data[{poly_select, coeff_index}];

    // Constrain coefficients to reasonable range
    genvar i;
    generate
        for (i = 0; i < 128; i = i + 1) begin : constrain_coeffs
            assume property (@(*)
                coeff_data[i][78:64] < 15'h7FFF);  // Not infinity/NaN
        end
    endgenerate
endmodule
```

**Effort**:
- Mockup: Low (30 minutes - create stub ROM)
- Production: Low-Medium (2-3 hours - convert to case statement ROM)

---

## **SUMMARY TABLE**

| Test | Issue | Mockup Viable? | Mockup Effort | Production Fix Effort | Recommendation |
|------|-------|----------------|---------------|----------------------|----------------|
| DCache2Way (×4) | Multiple drivers | ❌ Too complex | N/A | Medium (2-4h) | **Fix DUT** |
| FPU_Range_Reduction | Function complexity | ✅ Approximate | Low (1h) | Medium (4-6h) | **Mockup first, then fix** |
| FPU_Polynomial_Evaluator | ROM write enable | ✅ Perfect | Low (30min) | Low-Med (2-3h) | **Mockup (works as-is)** |

---

## **RECOMMENDED ACTION PLAN**

### Quick Wins (Mockups) - 90 minutes total:

1. **FPU_Polynomial_Evaluator** (30 min)
   - Create `FPU_Poly_Coeff_ROM_Formal.sv` stub
   - Modify `.sby` file to include stub
   - **Result**: Test should PASS

2. **FPU_Range_Reduction** (1 hour)
   - Add `fp_sub_formal()` function to wrapper
   - Replace function calls in formal configuration
   - **Result**: Test should PASS (with reduced accuracy checking)

### Production Fixes - 8-13 hours total:

3. **DCache2Way** (2-4 hours) - **HIGHEST PRIORITY**
   - Consolidate `wbuf_valid`, `just_finished_wbuf`, `eviction_started` logic
   - Requires careful analysis of state dependencies
   - Test extensively (cache bugs are catastrophic)
   - **Result**: All 4 DCache2Way variants PASS

4. **FPU_Range_Reduction** (4-6 hours) - **MEDIUM PRIORITY**
   - Replace `fp_sub()` function with `FPU_IEEE754_AddSub` module instantiation
   - Add state machine to handle multi-cycle subtraction
   - **Result**: Better accuracy + formal verification

5. **FPU_Polynomial_Evaluator** (2-3 hours) - **LOW PRIORITY**
   - Convert ROM to pure combinational `case` statement
   - Easier to maintain and synthesize
   - **Result**: Cleaner design + formal verification

---

## **EXPECTED FINAL RESULTS**

### With Mockups Only:
- **26/30 tests PASS** (86.7%)
- Remaining 4 errors: DCache2Way variants (requires DUT fix)

### With All Production Fixes:
- **30/30 tests PASS** (100%) 🎯
- Fully verified cache and FPU subsystems
- Production-ready formal verification suite
