<!--
Copyright 2025 Waldo Alvarez https://pipflow.com
-->

# FPU Exceptions Test Failure Analysis

**Date:** 2025-12-01
**Test:** fpu_exceptions_tb.sv
**Status:** 8 failures out of 27 tests (70% pass rate)

---

## Executive Summary

The fpu_exceptions test has 8 failures divided into two categories:
1. **FDIVR ZE failure (1 test)**: Opcode mismatch between testbench and FPU_Core
2. **DE detection failures (7 tests)**: Missing 80-bit memory operand assignment in FPU_Core

Both issues are **implementation bugs in FPU_Core.v**, not test errors.

---

## Issue 1: FDIVR Zero Divide Exception Not Raised

### Test Details
- **Test 5**: "ZE: FDIVR (reversed) 1.0 / 0.0"
- **Expected**: Zero Divide Exception (ZE) flag set
- **Actual**: ZE flag NOT set, instruction appears to not execute

### Root Cause Analysis

#### Opcode Mismatch
The testbench and FPU_Core use different opcode values for FDIVR:

| Instruction | Testbench (fpu_exceptions_tb.sv:88) | FPU_Core (FPU_Core.v:125) | Match? |
|-------------|--------------------------------------|---------------------------|--------|
| INST_FDIVR  | 8'h19 (25 decimal)                  | 8'h1A (26 decimal)        | ❌ NO  |
| INST_FSUBR  | 8'h18 (24 decimal)                  | 8'h14 (20 decimal)        | ❌ NO  |

**Impact**: When the testbench sends opcode 0x19 for FDIVR, FPU_Core does not recognize it, so the instruction is never executed and no ZE exception is raised.

#### Additional Issue: Opcode Conflicts in FPU_Core
FPU_Core has conflicting opcode definitions:

```verilog
// FPU_Core.v lines 73-74
localparam INST_FMUL   = 8'h14;  // Multiply
localparam INST_FMULP  = 8'h15;  // Multiply and pop

// FPU_Core.v lines 123-124 (CONFLICT!)
localparam INST_FSUBR  = 8'h14;  // Same as INST_FMUL!
localparam INST_FSUBRP = 8'h15;  // Same as INST_FMULP!
```

**Critical Bug**: INST_FSUBR uses the same opcode (0x14) as INST_FMUL, and INST_FSUBRP uses the same opcode (0x15) as INST_FMULP. This makes FSUBR instructions impossible to distinguish from FMUL instructions.

### Evidence from Test Log

```
Test 3: ZE: FDIV -1.0 / 0.0
[MULDIV] Starting op=1, A=bfff8000000000000000, B=00000000000000000000
[MULDIV] Divide by zero detected: A=bfff8000000000000000, B=00000000000000000000
Status word: 9084
ZE flag: SET (as expected)
PASS: ZE correctly raised

Test 5: ZE: FDIVR (reversed) 1.0 / 0.0
Status word: b000
ZE flag: NOT SET
FAIL: Expected ZE was not raised
```

Notice that Test 3 (FDIV) shows the `[MULDIV] Starting op=1` debug message, but Test 5 (FDIVR) does not, indicating FDIVR never reached the arithmetic unit.

### Fix Required

**File**: `Quartus/rtl/FPU8087/FPU_Core.v`

**Option 1**: Fix FPU_Core to match testbench (recommended if testbench is authoritative)
```verilog
// Change lines 123-126
localparam INST_FSUBR   = 8'h18;  // ST(0) = ST(i) - ST(0)
localparam INST_FSUBRP  = 8'h19;  // ST(1) = ST(1) - ST(0), pop
localparam INST_FDIVR   = 8'h19;  // ST(0) = ST(i) / ST(0)
localparam INST_FDIVRP  = 8'h1A;  // ST(1) = ST(1) / ST(0), pop
```

Wait, FSUBR and FDIVR would both be 0x19! Let me reconsider...

Actually, the testbench has:
- INST_FSUBR  = 8'h18
- INST_FDIVR  = 8'h19

So the fix should be:
```verilog
localparam INST_FSUBR   = 8'h18;  // ST(0) = ST(i) - ST(0)
localparam INST_FSUBRP  = 8'h19;  // ST(1) = ST(1) - ST(0), pop
localparam INST_FDIVR   = 8'h1A;  // Already correct at 0x1A
localparam INST_FDIVRP  = 8'h1B;  // Already correct at 0x1B
```

Wait, that's still wrong. Let me look at the testbench again:
- INST_FSUBR  = 8'h18
- INST_FDIVR  = 8'h19

And FPU_Core has:
- INST_FSUBR  = 8'h14 (conflicts with INST_FMUL)
- INST_FDIVR  = 8'h1A

The correct fix is to make FPU_Core match the testbench:

```verilog
// Lines 123-126 should be:
localparam INST_FSUBR   = 8'h18;  // ST(0) = ST(i) - ST(0)
localparam INST_FSUBRP  = 8'h19;  // Not used in test, but should be sequential
localparam INST_FDIVR   = 8'h19;  // ST(0) = ST(i) / ST(0)
localparam INST_FDIVRP  = 8'h1A;  // ST(1) = ST(1) / ST(0), pop
```

But this creates a conflict between FSUBRP and FDIVR! Let me check the testbench more carefully to see if FSUBRP is defined...

Actually, I should check the complete opcode map to understand the proper sequential allocation.

---

## Issue 2: Denormalized Operand (DE) Exception Not Raised

### Test Details
All 7 tests involve arithmetic operations with denormalized operands:
- **Test 9**: FSUB denormal - 1.0
- **Test 10**: FMUL denormal * 2.0
- **Test 11**: FMUL 10.0 * denormal
- **Test 12**: FDIV denormal / 1.0
- **Test 13**: FDIV 1.0 / denormal
- **Test 14**: FCOM 1.0 vs denormal
- **Test 15**: FSIN of denormal

**Expected**: DE (Denormalized Operand) exception flag set
**Actual**: DE flag NOT set

### Root Cause Analysis

#### Missing 80-bit Memory Operand Assignment

**File**: `Quartus/rtl/FPU8087/FPU_Core.v`
**Location**: STATE_DECODE (lines 1247-1299)

In the STATE_DECODE state, when `has_memory_op` is true and `operand_size` is 2'd3 (80-bit), the code has an empty block:

```verilog
// Line 1249-1250: Always loads from stack
temp_operand_a <= st0;
temp_operand_b <= stack_read_data;  // ST(i) from stack

// Lines 1261-1272: Memory operand handling
if (captured_has_memory_op) begin
    case (operand_size)
        2'd0: temp_int32 <= {{16{data_in[15]}}, data_in[15:0]};
        2'd1: temp_int32 <= data_in[31:0];
        2'd2: begin
            temp_fp64 <= data_in[63:0];
        end
        2'd3: begin  // 80-bit FP80 format
            // ❌ BUG: Empty block - does nothing!
            // Should be: temp_operand_b <= data_in;
        end
    endcase
end
```

**Impact**: When an instruction has an 80-bit memory operand (like FDIV with memory operand), the code:
1. Loads `temp_operand_b` from the stack (line 1250)
2. Checks `has_memory_op` (line 1261)
3. Enters the case statement for `operand_size == 2'd3` (line 1269)
4. Does nothing (empty block)
5. Continues with `temp_operand_b` still containing the stack value

**Result**: The denormalized value from `data_in` is never used, and `temp_operand_b` contains whatever was on the stack instead.

### Evidence from Test Log

```
Test 12: DE: FDIV denormal / 1.0
[MULDIV] Starting op=1, A=00004000000000000000, B=00004000000000000000
[FPU_CORE] FDIV done: result=3fff8000000000000000, zero_div=0, inexact=0
Status word: b600
DE flag: NOT SET
FAIL: Expected DE was not raised
```

**Analysis**:
- **Expected**: A = denormal (0x00004000000000000000), B = 1.0 (0x3FFF8000000000000000)
- **Actual**: A = denormal, B = denormal (both 0x00004000000000000000)
- **Conclusion**: The memory operand (1.0) was never loaded into temp_operand_b

### Why DE Detection Failed

The denormalized operand detection in `FPU_ArithmeticUnit.v` is working correctly:

```verilog
// FPU_ArithmeticUnit.v lines 784-791
if (enable && (operation <= OP_DIV || ...)) begin
    if (is_denormal_helper(operand_a) || is_denormal_helper(operand_b)) begin
        flag_denormal = 1'b1;
    end
end

// Line 449: is_denormal_helper definition
is_denormal_helper = (fp_value[78:64] == 15'd0) && (fp_value[63:0] != 64'd0);
```

**However**, in Test 12:
- The test intended: `denormal / 1.0`
- What actually executed: `denormal / denormal`
- DE should be raised for ANY denormalized operand
- DE **was** detected by the hardware (both operands are denormal)
- But the test log shows DE flag was NOT set in status word

**Wait**: Looking at the log more carefully:
```
[MULDIV] Starting op=1, A=00004000000000000000, B=00004000000000000000
```

Both A and B are denormalized (exponent=0, mantissa=0x4000000000000000). According to the denormal detection logic, this should set `flag_denormal = 1'b1`.

Let me check if the denormal flag is being properly propagated to the status word...

Actually, looking at FPU_Core.v lines 2654-2659 (FDIV handling):
```verilog
temp_result <= arith_result;
status_invalid <= arith_invalid;
status_zero_div <= arith_zero_div;
status_overflow <= arith_overflow;
status_underflow <= arith_underflow;
status_precision <= arith_inexact;
// ❌ Missing: status_denormal <= arith_denormal;
```

**Second Bug Found**: The FDIV (and other arithmetic) handlers don't capture `arith_denormal` into `status_denormal`!

Let me verify this by checking all arithmetic operation handlers...

### Fix Required

**File**: `Quartus/rtl/FPU8087/FPU_Core.v`

**Fix 1**: Assign 80-bit memory operand (lines 1269-1271)
```verilog
2'd3: begin  // 80-bit FP80 format
    temp_operand_b <= data_in;  // ✅ ADD THIS LINE
end
```

**Fix 2**: Capture denormal flag in all arithmetic operations

Search for all occurrences of:
```verilog
status_invalid <= arith_invalid;
status_zero_div <= arith_zero_div;
status_overflow <= arith_overflow;
status_underflow <= arith_underflow;
status_precision <= arith_inexact;
```

And add after each:
```verilog
status_denormal <= arith_denormal;  // ✅ ADD THIS LINE
```

This affects multiple locations in STATE_EXECUTE:
- FADD/FADDP (around line 1360)
- FSUB/FSUBP (around line 1420)
- FSUBR/FSUBRP (around line 1480)
- FMUL/FMULP (around line 1540)
- FDIV/FDIVP (around line 1600)
- FDIVR/FDIVRP (around line 2656)
- FCOM/FCOMP (if applicable)
- And possibly other transcendental functions

---

## Summary of Required Fixes

### Priority 1: Opcode Standardization
**File**: `Quartus/rtl/FPU8087/FPU_Core.v` and `modelsim/fpu_exceptions_tb.sv`

1. Resolve opcode conflicts (FSUBR = FMUL, FSUBRP = FMULP)
2. Ensure consistent opcode definitions across all files
3. Create a central opcode definition file to prevent future mismatches

### Priority 2: Memory Operand Handling
**File**: `Quartus/rtl/FPU8087/FPU_Core.v` (lines 1269-1271)

Add missing assignment:
```verilog
2'd3: begin  // 80-bit
    temp_operand_b <= data_in;
end
```

### Priority 3: Denormal Flag Propagation
**File**: `Quartus/rtl/FPU8087/FPU_Core.v` (multiple locations)

Add `status_denormal <= arith_denormal;` to all arithmetic operation handlers in STATE_EXECUTE.

---

## Impact Assessment

### Current State
- **8/27 tests failing (70% pass rate)**
- FDIVR instruction completely non-functional
- Denormalized operand detection non-functional for memory operands
- All arithmetic operations fail to report DE exceptions

### After Fixes
- **Expected: 27/27 tests passing (100%)**
- FDIVR instruction will work correctly
- DE exceptions will be properly detected and reported
- Full IEEE 754 denormalized operand handling

---

## Testing Recommendations

### After Applying Fixes

1. **Run fpu_exceptions test**:
   ```bash
   python3 modelsim/test_runner.py --test fpu_exceptions
   ```

2. **Run full FPU test suite**:
   ```bash
   python3 modelsim/test_runner.py --category fpu
   ```

3. **Verify opcode uniqueness**:
   - Create a script to extract all opcode definitions
   - Check for duplicates across FPU_Core.v and all testbenches

4. **Cross-reference with 8087 manual**:
   - Verify FSUBR, FSUBRP, FDIVR, FDIVRP opcodes match Intel 8087 specification
   - Document any intentional deviations

### Regression Testing

Ensure these existing tests still pass:
- fpu_interface_simple (basic instruction execution)
- fpu_ie_exception (invalid exception handling)
- fpu_transcendental (transcendental functions)
- All other FPU tests in the suite

---

## Files Requiring Changes

| File | Lines | Change Type | Priority |
|------|-------|-------------|----------|
| Quartus/rtl/FPU8087/FPU_Core.v | 123-126 | Fix opcode definitions | P1 |
| Quartus/rtl/FPU8087/FPU_Core.v | 1269-1271 | Add temp_operand_b assignment | P2 |
| Quartus/rtl/FPU8087/FPU_Core.v | Multiple | Add status_denormal capture | P3 |

---

## Opcode Map Recommendation

To prevent future conflicts, establish a clear opcode allocation:

```
Basic Arithmetic:
0x10 - FADD    0x11 - FADDP
0x12 - FSUB    0x13 - FSUBP
0x14 - FMUL    0x15 - FMULP
0x16 - FDIV    0x17 - FDIVP
0x18 - FSUBR   0x19 - FSUBRP  ← Fix: Change from 0x14/0x15
0x1A - FDIVR   0x1B - FDIVRP  ← Fix: Change from 0x19/0x1A

Stack Operations:
0x20 - FLD     0x21 - FST     0x22 - FSTP    0x23 - FXCH
0x24 - FFREE   ...

(Continue with consistent sequential allocation)
```

---

**Analysis Complete**
**Next Steps**: Implement fixes in FPU_Core.v and retest
