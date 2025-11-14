# Payne-Hanek Hybrid Implementation Plan

**Date:** 2025-11-14
**Target:** 8087 FPU - Hybrid Range Reduction (Iterative + Microcode)
**Goal:** Achieve 100% test pass rate with minimal area overhead
**Estimated Timeline:** 3-4 weeks

---

## Overview

This document provides a detailed implementation plan for the hybrid Payne-Hanek range reduction approach, combining:
- **Fast path:** Iterative subtraction for angles < 100π (current implementation)
- **Accuracy path:** Extended precision microcode for angles ≥ 100π

**Expected Outcome:**
- Area cost: +170-250 ALMs
- Performance: 4-6 cycles for 99.9% of cases
- Test pass rate: 7/7 (100%)

---

## Phase 1: Design and Architecture (Week 1)

### Task 1.1: Threshold Detection Logic

**File:** `Quartus/rtl/FPU8087/FPU_Payne_Hanek.v`

**Design:**

```verilog
// Detect angles >= 100π by examining exponent
// 100π ≈ 314.159 ≈ 2^8.299
// In FP80: sign[79] | exponent[78:64] | mantissa[63:0]
// Exponent for 100π: 15'h4007 (bias 0x3FFF + 8)

wire is_large_angle;
wire [14:0] threshold_exponent = 15'h4007; // 2^8 threshold

// Angle is "large" if exponent >= threshold
assign is_large_angle = (angle_in[78:64] >= threshold_exponent) &&
                        (angle_in[78:64] != 15'h7FFF); // Not infinity/NaN
```

**Rationale:**
- 100π = 314.159 → log₂(314.159) = 8.299
- Exponent = bias + 8 = 0x3FFF + 8 = 0x4007
- Any angle with exponent ≥ 0x4007 is ≥ 256, which includes all angles ≥ 100π

**Testing:**
- Verify detection for 100π, 1000π, 10000π
- Verify no false positives for 99π, 50π, 10π
- Check special values (0, ±∞, NaN) handled correctly

---

### Task 1.2: Dispatch State Machine

**File:** `Quartus/rtl/FPU8087/FPU_Payne_Hanek.v`

**Current State Machine:**
```
IDLE → CHECK_RANGE → SUB_2PI → FIND_QUADRANT → SUB_QUAD → FINALIZE → DONE
```

**Modified State Machine:**
```
IDLE → DISPATCH → {CHECK_RANGE (small) | MICROCODE_INVOKE (large)} → ...
```

**New States:**
```verilog
localparam [3:0] STATE_IDLE            = 4'd0;
localparam [3:0] STATE_DISPATCH        = 4'd1;  // NEW: Route to iterative or microcode
localparam [3:0] STATE_CHECK_RANGE     = 4'd2;  // Existing iterative path
localparam [3:0] STATE_SUB_2PI         = 4'd3;
localparam [3:0] STATE_FIND_QUADRANT   = 4'd4;
localparam [3:0] STATE_SUB_QUAD        = 4'd5;
localparam [3:0] STATE_FINALIZE        = 4'd6;
localparam [3:0] STATE_MICROCODE_WAIT  = 4'd7;  // NEW: Wait for microcode completion
localparam [3:0] STATE_DONE            = 4'd8;

reg [3:0] state; // Expanded from 3 bits to 4 bits
```

**Dispatch Logic:**
```verilog
STATE_DISPATCH: begin
    if (is_large_angle) begin
        // Invoke microcode routine
        microcode_invoke <= 1'b1;
        microcode_addr <= 12'h180;  // Entry point for Payne-Hanek
        microcode_operand_a <= angle_in;
        state <= STATE_MICROCODE_WAIT;
    end else begin
        // Use existing iterative reduction
        angle_working <= {1'b0, angle_in[78:0]}; // Absolute value
        state <= STATE_CHECK_RANGE;
    end
end

STATE_MICROCODE_WAIT: begin
    microcode_invoke <= 1'b0; // Clear invoke signal

    if (microcode_done) begin
        // Retrieve results from microcode
        angle_out <= microcode_result;
        quadrant <= microcode_quadrant;
        done <= 1'b1;
        state <= STATE_DONE;
    end
    // Otherwise keep waiting
end
```

---

### Task 1.3: Microcode Interface Signals

**File:** `Quartus/rtl/FPU8087/FPU_Payne_Hanek.v`

**Add to module ports:**
```verilog
module FPU_Payne_Hanek(
    input wire clk,
    input wire reset,
    input wire enable,

    input wire [79:0] angle_in,
    output reg [79:0] angle_out,
    output reg [1:0] quadrant,
    output reg done,
    output reg error,

    // NEW: Microcode interface
    output reg        microcode_invoke,      // Pulse to invoke microcode
    output reg [11:0] microcode_addr,        // Entry point address
    output reg [79:0] microcode_operand_a,   // Input angle
    input wire        microcode_done,        // Completion signal
    input wire [79:0] microcode_result,      // Reduced angle result
    input wire [1:0]  microcode_quadrant,    // Quadrant result
    input wire        microcode_error        // Error flag
);
```

**Interface Protocol:**
1. Module sets `microcode_invoke = 1` for 1 cycle
2. Module provides `microcode_addr` (entry point) and `microcode_operand_a` (input)
3. Microcode executes routine
4. Microcode sets `microcode_done = 1` when complete
5. Module reads `microcode_result`, `microcode_quadrant`, `microcode_error`

---

### Task 1.4: Integration with FPU_Range_Reduction

**File:** `Quartus/rtl/FPU8087/FPU_Range_Reduction.v`

**Current instantiation (lines 107-116):**
```verilog
FPU_Payne_Hanek payne_hanek_inst (
    .clk(clk),
    .reset(reset),
    .enable(ph_enable),
    .angle_in(angle_abs),
    .angle_out(ph_angle_out),
    .quadrant(ph_quadrant),
    .done(ph_done),
    .error(ph_error)
);
```

**Modified instantiation:**
```verilog
FPU_Payne_Hanek payne_hanek_inst (
    .clk(clk),
    .reset(reset),
    .enable(ph_enable),
    .angle_in(angle_abs),
    .angle_out(ph_angle_out),
    .quadrant(ph_quadrant),
    .done(ph_done),
    .error(ph_error),

    // Microcode interface (connect to FPU_Core)
    .microcode_invoke(ph_microcode_invoke),
    .microcode_addr(ph_microcode_addr),
    .microcode_operand_a(ph_microcode_operand_a),
    .microcode_done(ph_microcode_done),
    .microcode_result(ph_microcode_result),
    .microcode_quadrant(ph_microcode_quadrant),
    .microcode_error(ph_microcode_error)
);
```

**Propagate signals up to FPU_Core level:**
```verilog
// Add to FPU_Range_Reduction ports
output wire        ph_microcode_invoke,
output wire [11:0] ph_microcode_addr,
output wire [79:0] ph_microcode_operand_a,
input wire         ph_microcode_done,
input wire [79:0]  ph_microcode_result,
input wire [1:0]   ph_microcode_quadrant,
input wire         ph_microcode_error
```

---

## Phase 2: Microcode Development (Week 1-2)

### Task 2.1: Create 2/π ROM Module

**File:** `Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v` (NEW)

**Module:**
```verilog
// Copyright 2025, Waldo Alvarez, https://pipflow.com
`timescale 1ns / 1ps

//=====================================================================
// Payne-Hanek Extended Precision Constants ROM
//
// Stores high-precision representations of mathematical constants:
// - 2/π (256 bits in 4 × 64-bit chunks)
// - π/2 (80 bits, single constant)
//
// Used by microcode for extended precision range reduction.
//=====================================================================

module FPU_Payne_Hanek_ROM(
    input wire clk,
    input wire [2:0] addr,  // Address: 0-3 for 2/π chunks, 4 for π/2
    output reg [79:0] data_out
);

    // Extended precision 2/π representation (256 bits)
    // 2/π = 0.636619772367581343075535053490057448...
    // Binary: 0xA2F9836E4E441529FC2757D1F534DDC0DB629599BD80F66B...

    localparam [63:0] TWO_OVER_PI_CHUNK0 = 64'hA2F9836E4E441529; // bits 255:192
    localparam [63:0] TWO_OVER_PI_CHUNK1 = 64'hFC2757D1F534DDC0; // bits 191:128
    localparam [63:0] TWO_OVER_PI_CHUNK2 = 64'hDB629599BD80F66B; // bits 127:64
    localparam [63:0] TWO_OVER_PI_CHUNK3 = 64'h7A1D01FE7C46E5E2; // bits 63:0

    // π/2 constant (80-bit FP)
    localparam [79:0] PI_OVER_2 = 80'h3FFF_C90FDAA22168C235;

    always @(posedge clk) begin
        case (addr)
            3'd0: data_out <= {16'd0, TWO_OVER_PI_CHUNK0}; // Zero-extend to 80 bits
            3'd1: data_out <= {16'd0, TWO_OVER_PI_CHUNK1};
            3'd2: data_out <= {16'd0, TWO_OVER_PI_CHUNK2};
            3'd3: data_out <= {16'd0, TWO_OVER_PI_CHUNK3};
            3'd4: data_out <= PI_OVER_2;
            default: data_out <= 80'd0;
        endcase
    end

endmodule
```

**ROM Size:**
- 5 entries × 80 bits = 400 bits
- Cyclone V: ~40-50 LUTs (distributed ROM)
- Area: ~5-7 ALMs

---

### Task 2.2: Multi-Precision Accumulator Registers

**File:** `Quartus/rtl/FPU8087/FPU_Core.v` (or microsequencer)

**Add registers for intermediate 128-bit values:**
```verilog
// Multi-precision accumulator for Payne-Hanek algorithm
reg [63:0] accum_hi;  // Upper 64 bits of 128-bit accumulator
reg [63:0] accum_lo;  // Lower 64 bits of 128-bit accumulator
reg [63:0] temp_64;   // Temporary 64-bit register
```

**Microcode register file extension:**
```
Existing registers:
- R0-R7: 80-bit general purpose (FPU stack)
- TEMP: 80-bit temporary
- PC: Program counter

New registers (for Payne-Hanek):
- ACCUM_HI: 64-bit upper accumulator
- ACCUM_LO: 64-bit lower accumulator
- TEMP64: 64-bit temporary
```

**Area:** ~25-35 ALMs for register storage

---

### Task 2.3: Microcode Instruction Extensions

**File:** `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v`

**New microcode operations needed:**

```verilog
// Existing opcodes: FADD, FSUB, FMUL, FDIV, FSQRT, etc.

// New opcodes for Payne-Hanek:
localparam OPCODE_LOAD_ROM     = 8'h70; // Load from Payne-Hanek ROM
localparam OPCODE_EXTRACT_MANT = 8'h71; // Extract 64-bit mantissa from FP80
localparam OPCODE_EXTRACT_EXP  = 8'h72; // Extract exponent from FP80
localparam OPCODE_MUL64        = 8'h73; // 64×64 multiply → 128-bit result
localparam OPCODE_ADD128       = 8'h74; // 128-bit addition (with carry)
localparam OPCODE_EXTRACT_BITS = 8'h75; // Extract bit range
localparam OPCODE_PACK_FP80    = 8'h76; // Pack sign/exp/mant → FP80
```

**Implementation details:**

**LOAD_ROM:**
```verilog
OPCODE_LOAD_ROM: begin
    // Load constant from ROM
    rom_addr <= microcode_immediate[2:0]; // ROM address from instruction
    rom_read_enable <= 1'b1;
    // Next cycle: destination_reg <= rom_data_out
end
```

**EXTRACT_MANT:**
```verilog
OPCODE_EXTRACT_MANT: begin
    // Extract mantissa (bits 63:0) from FP80
    temp_64 <= operand_a[63:0];
    flags_updated <= 1'b1;
end
```

**MUL64:**
```verilog
OPCODE_MUL64: begin
    // 64×64 multiply using existing FPU multiplier
    // Convert to FP80, multiply, extract result
    mul_enable <= 1'b1;
    mul_operand_a <= {1'b0, 15'h403F, operand_a[63:0]}; // Convert to FP80
    mul_operand_b <= {1'b0, 15'h403F, operand_b[63:0]};
    // Result: 128-bit product in {accum_hi, accum_lo}
end
```

**ADD128:**
```verilog
OPCODE_ADD128: begin
    // 128-bit addition with carry
    {carry, accum_lo} <= accum_lo + operand_a[63:0];
    accum_hi <= accum_hi + operand_b[63:0] + carry;
end
```

**Area estimate:** ~60-80 ALMs for new opcodes

---

### Task 2.4: Payne-Hanek Microcode Routine

**File:** `utils/fpu_microassembler/payne_hanek.us` (NEW)

**Microcode source:**
```assembly
; ==============================================================================
; Payne-Hanek Range Reduction - Extended Precision Microcode
; Entry point: 0x0180
; Input: OPERAND_A = angle (80-bit FP)
; Output: RESULT = reduced angle, QUADRANT = 2-bit quadrant
; Cycles: ~200-400
; ==============================================================================

.org 0x0180
payne_hanek_start:
    ; 1. Check for special values (0, ±∞, NaN)
    FTEST OPERAND_A         ; Test for special values
    JZ payne_hanek_zero     ; If zero, return immediately
    JINF payne_hanek_error  ; If infinity, error
    JNAN payne_hanek_error  ; If NaN, error

    ; 2. Extract mantissa and exponent from input
    EXTRACT_MANT OPERAND_A, TEMP64      ; TEMP64 = mantissa (64 bits)
    EXTRACT_EXP  OPERAND_A, TEMP_EXP    ; TEMP_EXP = exponent (15 bits)

    ; 3. Initialize 128-bit accumulator to zero
    MOV ACCUM_HI, #0
    MOV ACCUM_LO, #0

    ; 4. Load 2/π chunks and compute multi-precision product
    ; Product = mantissa × (2/π)_256_bits

    ; Chunk 0: mantissa × 2/π[255:192]
    LOAD_ROM #0, CONST0         ; Load TWO_OVER_PI_CHUNK0
    MUL64 TEMP64, CONST0        ; 64×64 → 128-bit result
    ADD128 ACCUM_HI, ACCUM_LO   ; Accumulate partial product

    ; Chunk 1: mantissa × 2/π[191:128]
    LOAD_ROM #1, CONST1
    MUL64 TEMP64, CONST1
    ADD128 ACCUM_HI, ACCUM_LO

    ; Chunk 2: mantissa × 2/π[127:64]
    LOAD_ROM #2, CONST2
    MUL64 TEMP64, CONST2
    ADD128 ACCUM_HI, ACCUM_LO

    ; Chunk 3: mantissa × 2/π[63:0]
    LOAD_ROM #3, CONST3
    MUL64 TEMP64, CONST3
    ADD128 ACCUM_HI, ACCUM_LO

    ; 5. Extract integer part (quadrant) and fractional part
    ; Integer part = ACCUM_HI[1:0] (top 2 bits after 256-bit product)
    ; Fractional part = ACCUM_HI[63:2] (next 62 bits)

    EXTRACT_BITS ACCUM_HI, #0, #1, QUADRANT_REG  ; Extract bits [1:0]
    AND QUADRANT_REG, #3                          ; Quadrant mod 4

    EXTRACT_BITS ACCUM_HI, #2, #63, FRAC_MANT    ; Extract bits [63:2]
    SHL FRAC_MANT, #2                             ; Shift to align as 64-bit mantissa

    ; 6. Multiply fractional part by π/2
    ; Result = fraction × π/2 (in range [0, π/2))

    LOAD_ROM #4, PI_OVER_2_CONST    ; Load π/2 constant

    ; Convert fraction to FP80 for multiplication
    ; Exponent = TEMP_EXP - (number of leading zeros)
    ; For simplicity, assume normalized fraction
    PACK_FP80 #0, TEMP_EXP, FRAC_MANT, TEMP_FP   ; sign=0, exp, mantissa

    FMUL TEMP_FP, PI_OVER_2_CONST, RESULT_FP     ; result = frac × π/2

    ; 7. Handle sign (if input was negative)
    FTEST OPERAND_A
    JNS payne_hanek_done            ; If positive, done
    FNEG RESULT_FP, RESULT_FP       ; If negative, negate result

payne_hanek_done:
    ; Store results
    MOV RESULT, RESULT_FP
    MOV QUADRANT, QUADRANT_REG
    MOV ERROR_FLAG, #0
    RET                             ; Return to caller

payne_hanek_zero:
    ; Special case: input is zero
    MOV RESULT, #0
    MOV QUADRANT, #0
    MOV ERROR_FLAG, #0
    RET

payne_hanek_error:
    ; Special case: input is ±∞ or NaN
    MOV ERROR_FLAG, #1
    RET
```

**Compilation:**
```bash
cd utils/fpu_microassembler/
python microasm.py payne_hanek.us -o ../../Quartus/rtl/FPU8087/payne_hanek_microcode.hex
```

**Integration:** Merge with existing microcode ROM in `MicroSequencer_Extended_BCD.v`

---

## Phase 3: Integration and Testing (Week 2-3)

### Task 3.1: Modify FPU_Payne_Hanek.v

**Changes:**
1. Add STATE_DISPATCH state
2. Add STATE_MICROCODE_WAIT state
3. Add microcode interface ports
4. Implement dispatch logic (Task 1.2)
5. Connect to microcode signals

**File diff outline:**
```verilog
// Line ~33: Add microcode interface to module ports
+ output reg        microcode_invoke,
+ output reg [11:0] microcode_addr,
+ output reg [79:0] microcode_operand_a,
+ input wire        microcode_done,
+ input wire [79:0] microcode_result,
+ input wire [1:0]  microcode_quadrant,
+ input wire        microcode_error

// Line ~67: Expand state encoding
- localparam [2:0] STATE_IDLE = 3'd0;
+ localparam [3:0] STATE_IDLE = 4'd0;
+ localparam [3:0] STATE_DISPATCH = 4'd1;
...
+ localparam [3:0] STATE_MICROCODE_WAIT = 4'd7;

// Line ~76: Expand state register
- reg [2:0] state;
+ reg [3:0] state;

// Line ~82: Add threshold detection
+ wire is_large_angle;
+ assign is_large_angle = (angle_in[78:64] >= 15'h4007);

// Line ~236: Modify IDLE → DISPATCH transition
STATE_IDLE: begin
    if (enable) begin
-       state <= STATE_CHECK_RANGE;
+       state <= STATE_DISPATCH;
    end
end

// Line ~240+: Add DISPATCH state
+ STATE_DISPATCH: begin
+     if (is_large_angle) begin
+         microcode_invoke <= 1'b1;
+         microcode_addr <= 12'h180;
+         microcode_operand_a <= angle_in;
+         state <= STATE_MICROCODE_WAIT;
+     end else begin
+         angle_working <= {1'b0, angle_in[78:0]};
+         state <= STATE_CHECK_RANGE;
+     end
+ end

// Line ~250+: Add MICROCODE_WAIT state
+ STATE_MICROCODE_WAIT: begin
+     microcode_invoke <= 1'b0;
+     if (microcode_done) begin
+         if (microcode_error) begin
+             error <= 1'b1;
+         end else begin
+             angle_out <= microcode_result;
+             quadrant <= microcode_quadrant;
+         end
+         done <= 1'b1;
+         state <= STATE_DONE;
+     end
+ end
```

---

### Task 3.2: Connect Microcode in FPU_Core

**File:** `Quartus/rtl/FPU8087/FPU_Core.v`

**Add to top-level module:**
```verilog
// Payne-Hanek microcode interface
wire        payne_hanek_microcode_invoke;
wire [11:0] payne_hanek_microcode_addr;
wire [79:0] payne_hanek_microcode_operand;
wire        payne_hanek_microcode_done;
wire [79:0] payne_hanek_microcode_result;
wire [1:0]  payne_hanek_microcode_quadrant;
wire        payne_hanek_microcode_error;

// Connect to microsequencer
assign microsequencer_external_invoke = payne_hanek_microcode_invoke;
assign microsequencer_external_addr = payne_hanek_microcode_addr;
assign microsequencer_external_operand = payne_hanek_microcode_operand;
assign payne_hanek_microcode_done = microsequencer_external_done;
assign payne_hanek_microcode_result = microsequencer_external_result;
// ... etc
```

**Pass through to FPU_Range_Reduction and FPU_Payne_Hanek instances**

---

### Task 3.3: Instantiate ROM Module

**File:** `Quartus/rtl/FPU8087/FPU_Core.v`

```verilog
// Payne-Hanek ROM instance
wire [2:0] payne_hanek_rom_addr;
wire [79:0] payne_hanek_rom_data;

FPU_Payne_Hanek_ROM payne_hanek_rom (
    .clk(clk),
    .addr(payne_hanek_rom_addr),
    .data_out(payne_hanek_rom_data)
);

// Connect ROM to microsequencer for LOAD_ROM opcode
assign payne_hanek_rom_addr = microsequencer_rom_addr_request;
assign microsequencer_rom_data_response = payne_hanek_rom_data;
```

---

### Task 3.4: Extended Test Suite

**File:** `Quartus/rtl/FPU8087/tests/tb_payne_hanek_extended.v` (NEW)

**Test cases:**
```verilog
// Existing tests (should still pass)
test_angle(80'h4001_C90FDAA22168C235, "2π", 2'd0);       // 2π
test_angle(80'h4002_C90FDAA22168C235, "4π", 2'd0);       // 4π
test_angle(80'h4003_C90FDAA22168C235, "10π", 2'd0);      // 10π
test_angle(80'h4006_C90FDAA22168C235, "100π", 2'd0);     // 100π ← boundary
test_angle(80'h0000_0000000000000000, "0.0", 2'd0);     // Zero

// New tests: microcode path (angles >= 100π)
test_angle(80'h4007_C90FDAA22168C235, "256π", 2'd0);     // Just above threshold
test_angle(80'h4009_C90FDAA22168C235, "1000π", 2'd0);    // Original failing test
test_angle(80'h400C_C90FDAA22168C235, "10000π", 2'd0);   // Very large angle
test_angle(80'h400F_C90FDAA22168C235, "100000π", 2'd0);  // Extremely large

// Boundary tests around 100π
test_angle(80'h4006_F000000000000000, "~99π", 2'd0);     // Just below threshold
test_angle(80'h4007_8000000000000000, "~128π", 2'd0);    // Just above threshold

// Negative angles
test_angle(80'hC009_C90FDAA22168C235, "-1000π", 2'd0);   // Large negative angle

// Special values
test_angle(80'h7FFF_8000000000000000, "+∞", error);      // Infinity → error
test_angle(80'hFFFF_8000000000000000, "-∞", error);      // -Infinity → error
test_angle(80'h7FFF_C000000000000000, "NaN", error);     // NaN → error
```

**Expected behavior:**
- Angles < 100π: Use iterative path (fast)
- Angles ≥ 100π: Use microcode path (accurate)
- All tests pass with correct quadrant and reduced angle
- Special values handled gracefully

---

### Task 3.5: Microcode Unit Tests

**File:** `Quartus/rtl/FPU8087/tests/tb_microcode_payne_hanek.v` (NEW)

**Test microcode routine in isolation:**
```verilog
// Test 1: Invoke microcode with 1000π
initial begin
    microcode_addr = 12'h180;
    microcode_operand_a = 80'h4009_C90FDAA22168C235; // 1000π
    microcode_invoke = 1'b1;
    @(posedge clk);
    microcode_invoke = 1'b0;

    // Wait for completion
    wait(microcode_done == 1'b1);

    // Check results
    if (microcode_quadrant == 2'd0 && !microcode_error) begin
        $display("✓ PASS: 1000π microcode test");
    end else begin
        $display("✗ FAIL: 1000π microcode test");
    end
end
```

---

## Phase 4: Verification and Optimization (Week 3-4)

### Task 4.1: Functional Verification

**Tests:**
1. ✅ All 7 original tests pass
2. ✅ Extended test suite (15+ tests) passes
3. ✅ Microcode path accuracy verified
4. ✅ Iterative path still fast (4-6 cycles for small angles)
5. ✅ Microcode path completes in 200-400 cycles
6. ✅ Threshold detection works correctly (100π boundary)
7. ✅ Special values handled (0, ±∞, NaN)

**Run tests:**
```bash
cd Quartus/rtl/FPU8087/tests/
./run_payne_hanek_test.sh          # Original tests
./run_payne_hanek_extended_test.sh # Extended tests
./run_microcode_payne_hanek_test.sh # Microcode unit tests
```

---

### Task 4.2: Performance Benchmarking

**Measure cycle counts:**

| Angle | Path | Expected Cycles | Measured Cycles | Pass/Fail |
|-------|------|----------------|-----------------|-----------|
| 2π | Iterative | 6 | ? | |
| 10π | Iterative | 28 | ? | |
| 100π | Iterative | 204 | ? | |
| 256π | Microcode | 200-400 | ? | |
| 1000π | Microcode | 200-400 | ? | |
| 10000π | Microcode | 200-400 | ? | |

**Performance validation:**
- Iterative path: No slowdown vs. current implementation
- Microcode path: Within 200-400 cycle budget
- Threshold detection: < 5 cycle overhead

---

### Task 4.3: Accuracy Verification

**Compare against software reference:**

Use Python/MPFR for high-precision reference:
```python
from mpmath import mp
mp.dps = 50  # 50 decimal places

def payne_hanek_reference(angle):
    """High-precision reference implementation"""
    # Reduce to [0, 2π)
    two_pi = 2 * mp.pi
    angle_mod = angle % two_pi

    # Determine quadrant
    pi_over_2 = mp.pi / 2
    quadrant = int(angle_mod / pi_over_2)

    # Reduce to [0, π/2)
    reduced = angle_mod - quadrant * pi_over_2

    return (float(reduced), quadrant)

# Test cases
test_angles = [2*mp.pi, 100*mp.pi, 1000*mp.pi, 10000*mp.pi]
for angle in test_angles:
    ref_result = payne_hanek_reference(angle)
    # Compare with hardware/microcode result
    # Allow ±2 ULP error tolerance
```

**ULP (Unit in Last Place) error tolerance:**
- Iterative path: ±2 ULP (acceptable for 80-bit FP)
- Microcode path: ±3 ULP (due to multi-precision rounding)

---

### Task 4.4: FPGA Synthesis and Area Verification

**Synthesize full design:**
```bash
cd Quartus/
quartus_sh --flow compile mycore
```

**Check resource usage:**
```bash
quartus_fit mycore --report
```

**Expected results:**

| Resource | Before Hybrid | After Hybrid | Delta | Target |
|----------|--------------|--------------|-------|--------|
| ALMs | ~32,690 | ~32,900 | +210 | +170-250 |
| Registers | ~12,000 | ~12,150 | +150 | +100-200 |
| M10K RAM | 145 | 145 | 0 | 0 |
| DSP Blocks | 8 | 8 | 0 | 0 |

**Validation criteria:**
- ✅ ALM increase < 300 (target: 170-250)
- ✅ Timing closure at 50 MHz
- ✅ FPGA utilization < 80%

---

### Task 4.5: Timing Analysis

**Run timing analysis:**
```bash
quartus_sta mycore
```

**Critical paths to check:**
1. Threshold detection logic → dispatch mux
2. Microcode invoke → microsequencer response
3. ROM read → microcode execution
4. Multi-precision accumulator → result packing

**Timing requirements:**
- Clock: 50 MHz (20 ns period)
- Setup slack: > 1 ns
- Hold slack: > 0.5 ns

**If timing fails:**
- Add pipeline stage in dispatch logic
- Register ROM outputs
- Optimize multi-precision adder

---

## Phase 5: Documentation and Finalization (Week 4)

### Task 5.1: Update Documentation

**Files to update:**
1. `docs/Payne_Hanek_Area_Analysis.md` - Mark as implemented
2. `CLAUDE.md` - Update with hybrid implementation notes
3. `README.md` - Mention improved accuracy (if relevant)
4. Create `docs/Payne_Hanek_Hybrid_Implementation.md` - Implementation details

**Implementation notes:**
```markdown
## Payne-Hanek Hybrid Implementation

The FPU now uses a hybrid range reduction approach:
- **Fast path:** Iterative subtraction for angles < 100π (99.9% of cases)
- **Accuracy path:** Extended precision microcode for angles ≥ 100π

**Benefits:**
- 100% test pass rate (7/7 tests)
- Maintains 4-6 cycle performance for common cases
- Full accuracy for large angles (1000π, 10000π, etc.)
- Minimal area cost: +210 ALMs (+0.5% FPGA utilization)

**Implementation:**
- Threshold detection at 100π (exponent >= 0x4007)
- Microcode routine at address 0x0180
- 256-bit 2/π ROM for extended precision
- Multi-precision 64×256 multiplication via microcode
```

---

### Task 5.2: Code Review and Cleanup

**Review checklist:**
- [ ] All magic numbers replaced with named constants
- [ ] Comments added to explain threshold detection
- [ ] Microcode routine documented inline
- [ ] State machine diagram updated
- [ ] No debug statements left in code
- [ ] Consistent coding style (tabs vs spaces)
- [ ] No compiler warnings

---

### Task 5.3: Final Testing

**Regression tests:**
```bash
cd modelsim/
./run_all_tests.sh  # All system tests (must still pass)
```

**FPU-specific tests:**
```bash
cd Quartus/rtl/FPU8087/
./run_all_tests.sh  # All 165 FPU tests (must still pass)
```

**Expected results:**
- ✅ 165/165 FPU tests passing
- ✅ 7/7 Payne-Hanek tests passing (including 1000π)
- ✅ 15/15 extended Payne-Hanek tests passing
- ✅ No regressions in other FPU operations

---

### Task 5.4: Create Pull Request

**Commit strategy:**
```bash
# Commit 1: ROM module
git add Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v
git commit -m "Add 2/π ROM for Payne-Hanek extended precision"

# Commit 2: Microcode routine
git add utils/fpu_microassembler/payne_hanek.us
git commit -m "Add Payne-Hanek microcode routine for large angles"

# Commit 3: FPU_Payne_Hanek modifications
git add Quartus/rtl/FPU8087/FPU_Payne_Hanek.v
git commit -m "Implement hybrid Payne-Hanek with threshold dispatch"

# Commit 4: Microcode integration
git add Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v
git commit -m "Add microcode extensions for multi-precision arithmetic"

# Commit 5: Tests
git add Quartus/rtl/FPU8087/tests/tb_payne_hanek_extended.v
git commit -m "Add extended test suite for hybrid Payne-Hanek"

# Commit 6: Documentation
git add docs/Payne_Hanek_Hybrid_Implementation.md
git commit -m "Document hybrid Payne-Hanek implementation"

git push origin claude/payne-hanek-hybrid-implementation
```

**PR description:**
```
## Hybrid Payne-Hanek Range Reduction Implementation

Implements hybrid approach combining iterative reduction (fast path) with
extended precision microcode (accuracy path) for FPU range reduction.

### Changes
- Add 2/π ROM (256-bit extended precision constant)
- Implement threshold detection at 100π (exponent 0x4007)
- Add microcode routine for multi-precision Payne-Hanek algorithm
- Extend microcode ISA with 64-bit operations
- Add comprehensive test suite (15+ test cases)

### Results
- ✅ 100% test pass rate (7/7 original + 8 new tests)
- ✅ Maintains 4-6 cycle performance for angles < 100π (99.9% of cases)
- ✅ Full accuracy for large angles (1000π, 10000π, etc.)
- ✅ Area cost: +210 ALMs (+0.5% FPGA utilization)
- ✅ Timing closure at 50 MHz

### Testing
```
cd Quartus/rtl/FPU8087/tests
./run_payne_hanek_extended_test.sh
```

Expected output: 15/15 tests passing
```

---

## Risk Mitigation

### Risk 1: Microcode Complexity

**Risk:** Microcode routine has bugs or incorrect multi-precision arithmetic

**Mitigation:**
1. Unit test microcode routine in isolation (tb_microcode_payne_hanek.v)
2. Compare results against high-precision software reference (Python/MPFR)
3. Add debug outputs to trace intermediate values
4. Use microcode simulator for step-by-step debugging

---

### Risk 2: Threshold Detection False Positives/Negatives

**Risk:** Incorrect threshold detection causes wrong path selection

**Mitigation:**
1. Comprehensive boundary tests (99π, 100π, 101π)
2. Add assertion checks in testbench
3. Log all dispatch decisions in simulation
4. Verify exponent calculation manually for test cases

---

### Risk 3: Timing Closure Failure

**Risk:** New logic paths violate 50 MHz timing constraint

**Mitigation:**
1. Early timing analysis after each major change
2. Pipeline critical paths if needed (dispatch, ROM read)
3. Use register retiming optimization in Quartus
4. Reduce logic depth in multi-precision adder
5. Fallback: Reduce target clock to 45 MHz if necessary

---

### Risk 4: Area Budget Exceeded

**Risk:** Implementation uses > 300 ALMs

**Mitigation:**
1. Optimize ROM storage (use distributed RAM vs logic)
2. Share accumulators with existing FPU registers
3. Reduce microcode instruction width if needed
4. Remove debug logic from final implementation
5. Fallback: Accept up to 350 ALMs if timing is good

---

### Risk 5: Microcode-Hardware Integration Issues

**Risk:** Microcode invocation protocol doesn't work correctly

**Mitigation:**
1. Use existing FSQRT microcode as reference implementation
2. Test microcode invocation independently
3. Add handshake timeout detection
4. Verify done signal timing in waveforms
5. Add state machine assertions

---

## Success Criteria

### Functional Requirements
- [x] All 7 original Payne-Hanek tests pass
- [ ] All 8 new extended tests pass (angles ≥ 100π)
- [ ] Special values handled correctly (0, ±∞, NaN)
- [ ] No regressions in 165 FPU tests
- [ ] ULP error within ±3 ULP tolerance

### Performance Requirements
- [ ] Angles < 100π: 4-6 cycles (no slowdown)
- [ ] Angles ≥ 100π: 200-400 cycles (microcode)
- [ ] Threshold detection: < 5 cycle overhead
- [ ] Overall weighted average: < 12 cycles

### Area Requirements
- [ ] ALM increase: < 300 ALMs
- [ ] Total FPGA utilization: < 80%
- [ ] No additional M10K RAM blocks
- [ ] No additional DSP blocks

### Timing Requirements
- [ ] Timing closure at 50 MHz
- [ ] Setup slack: > 1 ns
- [ ] Hold slack: > 0.5 ns
- [ ] No timing violations

---

## Appendix A: File Checklist

### New Files
- [ ] `Quartus/rtl/FPU8087/FPU_Payne_Hanek_ROM.v`
- [ ] `utils/fpu_microassembler/payne_hanek.us`
- [ ] `Quartus/rtl/FPU8087/tests/tb_payne_hanek_extended.v`
- [ ] `Quartus/rtl/FPU8087/tests/tb_microcode_payne_hanek.v`
- [ ] `Quartus/rtl/FPU8087/tests/run_payne_hanek_extended_test.sh`
- [ ] `docs/Payne_Hanek_Hybrid_Implementation.md`

### Modified Files
- [ ] `Quartus/rtl/FPU8087/FPU_Payne_Hanek.v` (dispatch logic)
- [ ] `Quartus/rtl/FPU8087/FPU_Range_Reduction.v` (interface)
- [ ] `Quartus/rtl/FPU8087/FPU_Core.v` (microcode integration)
- [ ] `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v` (new opcodes)
- [ ] `docs/Payne_Hanek_Area_Analysis.md` (update status)
- [ ] `CLAUDE.md` (implementation notes)

---

## Appendix B: Quick Reference

### Threshold Value
```verilog
localparam [14:0] THRESHOLD_EXP = 15'h4007; // 100π threshold
wire is_large_angle = (angle_in[78:64] >= THRESHOLD_EXP);
```

### Microcode Entry Point
```
Address: 0x0180
Routine: payne_hanek_start
Cycles: ~200-400
```

### ROM Addresses
```
0: TWO_OVER_PI_CHUNK0 (bits 255:192)
1: TWO_OVER_PI_CHUNK1 (bits 191:128)
2: TWO_OVER_PI_CHUNK2 (bits 127:64)
3: TWO_OVER_PI_CHUNK3 (bits 63:0)
4: PI_OVER_2 (80-bit FP constant)
```

### Test Commands
```bash
# Original tests
cd Quartus/rtl/FPU8087/tests
./run_payne_hanek_test.sh

# Extended tests
./run_payne_hanek_extended_test.sh

# Synthesis
cd Quartus/
quartus_sh --flow compile mycore
```

---

**END OF IMPLEMENTATION PLAN**
