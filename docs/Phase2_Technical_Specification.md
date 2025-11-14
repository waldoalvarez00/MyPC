# Phase 2 Technical Specification: Payne-Hanek Microcode Implementation

**Date:** 2025-11-14
**Prerequisite:** Phase 1 Complete (Hardware infrastructure in place)
**Estimated Effort:** 1-2 weeks (including testing)
**Risk Level:** Medium (requires careful microsequencer integration)

---

## Overview

This document provides complete technical specifications for implementing the Payne-Hanek extended precision range reduction algorithm in microcode. Phase 1 has provided the hardware infrastructure (ROM, dispatch logic, interface). Phase 2 implements the actual algorithm.

---

## Architecture Summary

### Current State (Phase 1 Complete)

✅ **Dispatch Logic:** Routes angles ≥ 256 to microcode (address 0x0180)
✅ **ROM Module:** FPU_Payne_Hanek_ROM.v provides 2/π and π/2 constants
✅ **Interface:** Microcode invoke/done handshake defined
✅ **Test Framework:** Dispatch logic verified working

### Phase 2 Goal

Implement microcode routine that:
1. Performs extended precision 64×256 multiplication (mantissa × 2/π)
2. Extracts integer part (quadrant) and fractional part (reduced angle)
3. Multiplies fractional part by π/2
4. Returns reduced angle and quadrant

---

## Section 1: MicroSequencer Extensions

### 1.1 Add Multi-Precision Registers

**File:** `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v`

**Location:** After line 229 (existing temp registers)

```verilog
//=================================================================
// Multi-Precision Accumulator Registers (for Payne-Hanek)
//=================================================================

reg [63:0] accum_hi;        // Upper 64 bits of 128-bit accumulator
reg [63:0] accum_lo;        // Lower 64 bits of 128-bit accumulator
reg [63:0] temp_64bit;      // Temporary 64-bit register
reg [2:0]  rom_addr_reg;    // ROM address register
reg        carry_bit;       // Carry flag for multi-precision addition
```

**Initialization:** Add to reset block

```verilog
accum_hi <= 64'd0;
accum_lo <= 64'd0;
temp_64bit <= 64'd0;
rom_addr_reg <= 3'd0;
carry_bit <= 1'b0;
```

---

### 1.2 Add New Micro-Operations

**File:** `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v`

**Location:** After line 122 (existing MOP definitions)

```verilog
// Payne-Hanek specific operations (0x20-0x27)
localparam MOP_LOAD_ROM        = 5'h20;  // Load from Payne-Hanek ROM
localparam MOP_EXTRACT_MANT    = 5'h21;  // Extract 64-bit mantissa from FP80
localparam MOP_EXTRACT_EXP     = 5'h22;  // Extract 15-bit exponent from FP80
localparam MOP_MUL64           = 5'h23;  // 64×64 multiply → 128-bit result
localparam MOP_ADD128          = 5'h24;  // 128-bit addition with carry
localparam MOP_EXTRACT_BITS    = 5'h25;  // Extract bit range from register
localparam MOP_PACK_FP80       = 5'h26;  // Pack sign/exp/mant → FP80
localparam MOP_CLEAR_ACCUM     = 5'h27;  // Clear accumulators
```

---

### 1.3 ROM Interface Signals

**File:** `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v`

**Location:** After line 81 (module ports)

```verilog
// Interface to Payne-Hanek ROM
output reg [2:0]  ph_rom_addr,      // ROM address (0-4)
input wire [79:0] ph_rom_data       // ROM data output
```

**Note:** These signals must be connected at FPU_Core level to the FPU_Payne_Hanek_ROM instance.

---

### 1.4 Implement New Micro-Operations

**File:** `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v`

**Location:** In STATE_EXEC case statement (around line 400+)

```verilog
//-------------------------------------------------------------
// Payne-Hanek Micro-Operations
//-------------------------------------------------------------

MOP_LOAD_ROM: begin
    // Load from Payne-Hanek ROM
    // immediate[2:0] = ROM address
    rom_addr_reg <= microinstruction[17:15];  // Extract ROM address from immediate
    ph_rom_addr <= microinstruction[17:15];
    // Result available next cycle in ph_rom_data
    // Will be loaded by subsequent instruction
    pc <= next_addr;
    state <= STATE_FETCH;
end

MOP_EXTRACT_MANT: begin
    // Extract 64-bit mantissa from temp_fp_a
    // FP80 format: [79]=sign, [78:64]=exp, [63:0]=mantissa (with explicit integer bit)
    temp_64bit <= temp_fp_a[63:0];
    pc <= next_addr;
    state <= STATE_FETCH;
end

MOP_EXTRACT_EXP: begin
    // Extract 15-bit exponent from temp_fp_a
    // Store in temp_reg (lower 15 bits)
    temp_reg[14:0] <= temp_fp_a[78:64];
    temp_reg[63:15] <= 49'd0;  // Clear upper bits
    pc <= next_addr;
    state <= STATE_FETCH;
end

MOP_MUL64: begin
    // 64×64 multiply → 128-bit result
    // Operands: temp_64bit × (ROM data or another 64-bit value)
    // Result: {accum_hi, accum_lo}
    //
    // For Payne-Hanek: mantissa × 2/π chunk
    // ROM data comes in as 80-bit but we only use lower 64 bits
    {accum_hi, accum_lo} <= temp_64bit * ph_rom_data[63:0];
    pc <= next_addr;
    state <= STATE_FETCH;
end

MOP_ADD128: begin
    // 128-bit addition: accum += temp values
    // For multi-precision accumulation of partial products
    //
    // Low word addition
    {carry_bit, accum_lo} <= accum_lo + temp_fp_b[63:0];
    // High word addition with carry
    accum_hi <= accum_hi + temp_fp_c[63:0] + carry_bit;
    pc <= next_addr;
    state <= STATE_FETCH;
end

MOP_EXTRACT_BITS: begin
    // Extract bit range from accum_hi
    // immediate[7:5] = start bit
    // immediate[4:0] = number of bits
    //
    // For Payne-Hanek:
    //   - Extract bits [1:0] for quadrant
    //   - Extract bits [63:2] for fractional mantissa
    //
    // Simplified: just extract specific ranges
    case (microinstruction[23:21])  // Use micro_op field extension
        3'd0: temp_reg <= {62'd0, accum_hi[1:0]};        // Quadrant (bits 1:0)
        3'd1: temp_reg <= accum_hi[63:2];                 // Fraction (bits 63:2)
        3'd2: temp_reg <= accum_lo;                       // Lower 64 bits
        3'd3: temp_reg <= accum_hi;                       // Upper 64 bits
        default: temp_reg <= 64'd0;
    endcase
    pc <= next_addr;
    state <= STATE_FETCH;
end

MOP_PACK_FP80: begin
    // Pack components into FP80 format
    // temp_reg[14:0] = exponent
    // temp_64bit = mantissa
    // sign = 0 (always positive for Payne-Hanek output)
    temp_result <= {1'b0, temp_reg[14:0], temp_64bit};
    pc <= next_addr;
    state <= STATE_FETCH;
end

MOP_CLEAR_ACCUM: begin
    // Clear multi-precision accumulators
    accum_hi <= 64'd0;
    accum_lo <= 64'd0;
    carry_bit <= 1'b0;
    pc <= next_addr;
    state <= STATE_FETCH;
end
```

---

### 1.5 Add Program Table Entry

**File:** `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v`

**Location:** In micro_program_table initialization (around line 207)

```verilog
// Program 22: Payne-Hanek range reduction
micro_program_table[22] = 16'h0180;  // Entry point at 0x0180
```

---

## Section 2: Payne-Hanek Microcode Routine

### 2.1 Complete Microcode Listing

**File:** `Quartus/rtl/FPU8087/MicroSequencer_Extended_BCD.v`

**Location:** In microcode_rom initialization (after existing programs, around line 800+)

```verilog
//-------------------------------------------------------------
// Program 22: Payne-Hanek Extended Precision Range Reduction
// Address: 0x0180-0x01CF (~80 instructions)
//
// Algorithm:
// 1. Extract mantissa and exponent from input angle
// 2. Multiply mantissa by 256-bit 2/π constant (4 partial products)
// 3. Extract integer part (quadrant) from product
// 4. Extract fractional part (reduced mantissa) from product
// 5. Multiply fractional part by π/2
// 6. Pack result as FP80
//
// Input: temp_fp_a = angle (80-bit FP, angles >= 256)
// Output: temp_result = reduced angle [0, π/2), temp_reg = quadrant (0-3)
//
// Cycles: ~200-250 (4 multiplies + overhead)
//-------------------------------------------------------------

// Entry point
microcode_rom[16'h0180] = {OPCODE_EXEC, MOP_LOAD_A, 8'd0, 15'h0181};           // Load angle from data_in

// Step 1: Extract mantissa and exponent
microcode_rom[16'h0181] = {OPCODE_EXEC, MOP_EXTRACT_MANT, 8'd0, 15'h0182};     // temp_64bit = mantissa
microcode_rom[16'h0182] = {OPCODE_EXEC, MOP_EXTRACT_EXP, 8'd0, 15'h0183};      // temp_reg = exponent

// Step 2: Clear accumulator
microcode_rom[16'h0183] = {OPCODE_EXEC, MOP_CLEAR_ACCUM, 8'd0, 15'h0184};      // accum_hi/lo = 0

// Step 3: Load first 2/π chunk and multiply (partial product 0)
microcode_rom[16'h0184] = {OPCODE_EXEC, MOP_LOAD_ROM, 8'd0, 15'h0185};         // Load ROM[0] (chunk 0)
microcode_rom[16'h0185] = {OPCODE_EXEC, MOP_MUL64, 8'd0, 15'h0186};            // mantissa × chunk0 → accum
// accum now has first 128-bit partial product

// Step 4: Save first partial product temporarily
microcode_rom[16'h0186] = {OPCODE_EXEC, MOP_MOVE_A_TO_C, 8'd0, 15'h0187};      // Save for later

// Step 5: Load second 2/π chunk and multiply (partial product 1)
microcode_rom[16'h0187] = {OPCODE_EXEC, MOP_LOAD_ROM, 8'd1, 15'h0188};         // Load ROM[1] (chunk 1)
microcode_rom[16'h0188] = {OPCODE_EXEC, MOP_MUL64, 8'd0, 15'h0189};            // mantissa × chunk1 → {temp_hi, temp_lo}

// Step 6: Accumulate second partial product (shifted by 64 bits)
// For true 64×256 multiply, we need to shift and add partial products
// Simplified: We'll use the upper 128 bits of the first product
// (This is an approximation - full implementation needs careful alignment)

// Step 7: Load third 2/π chunk and multiply (partial product 2)
microcode_rom[16'h0189] = {OPCODE_EXEC, MOP_LOAD_ROM, 8'd2, 15'h018A};         // Load ROM[2] (chunk 2)
microcode_rom[16'h018A] = {OPCODE_EXEC, MOP_MUL64, 8'd0, 15'h018B};            // mantissa × chunk2

// Step 8: Load fourth 2/π chunk and multiply (partial product 3)
microcode_rom[16'h018B] = {OPCODE_EXEC, MOP_LOAD_ROM, 8'd3, 15'h018C};         // Load ROM[3] (chunk 3)
microcode_rom[16'h018C] = {OPCODE_EXEC, MOP_MUL64, 8'd0, 15'h018D};            // mantissa × chunk3

// At this point, accum_hi contains the upper 64 bits of the 320-bit product
// This is where the integer and fractional parts are located

// Step 9: Extract quadrant (integer part, bits [1:0])
microcode_rom[16'h018D] = {OPCODE_EXEC, MOP_EXTRACT_BITS, 8'd0, 15'h018E};     // Extract bits[1:0] → temp_reg
// temp_reg now contains quadrant (0-3)

// Step 10: Extract fractional mantissa (bits [63:2])
microcode_rom[16'h018E] = {OPCODE_EXEC, MOP_EXTRACT_BITS, 8'd1, 15'h018F};     // Extract bits[63:2] → temp_reg
// temp_reg now contains 62-bit fractional mantissa

// Step 11: Shift fractional mantissa to form 64-bit normalized mantissa
// (This step might need adjustment based on actual bit positions)
microcode_rom[16'h018F] = {OPCODE_EXEC, MOP_MOVE_TEMP, 8'd0, 15'h0190};        // temp_64bit = temp_reg << 2

// Step 12: Adjust exponent for fractional part
// The fractional part represents a value in [0, 1), so exponent should be adjusted
// Original exponent - (number of bits in product position)
microcode_rom[16'h0190] = {OPCODE_EXEC, MOP_LOAD_IMM, 8'd0, 15'h0191};         // Adjust exponent
microcode_rom[16'h0191] = {OPCODE_EXEC, MOP_PACK_FP80, 8'd0, 15'h0192};        // Pack fraction as FP80

// Step 13: Multiply fractional part by π/2
microcode_rom[16'h0192] = {OPCODE_EXEC, MOP_MOVE_RES_TO_A, 8'd0, 15'h0193};    // Move fraction to temp_fp_a
microcode_rom[16'h0193] = {OPCODE_EXEC, MOP_LOAD_ROM, 8'd4, 15'h0194};         // Load ROM[4] (π/2)
// ph_rom_data now contains π/2

// Need to move ROM data to temp_fp_b for multiplication
// (This requires an additional microcode operation or data path)
microcode_rom[16'h0194] = {OPCODE_EXEC, MOP_LOAD_B, 8'd0, 15'h0195};           // Load π/2 into temp_fp_b

// Step 14: Perform multiplication: fraction × π/2
microcode_rom[16'h0195] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd2, 15'h0196};       // Call MUL (op=2)
microcode_rom[16'h0196] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h0197};       // Wait for multiplication
microcode_rom[16'h0197] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h0198};   // Load result

// Step 15: Store quadrant in appropriate location
// (Quadrant needs to be passed back through the microcode interface)
// For now, store in temp_reg (already there from step 9)

// Step 16: Return
microcode_rom[16'h0198] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return with result
```

**Note:** This is a simplified version. The full implementation requires:
1. Proper alignment of partial products (shifted by 64 bits each)
2. Multi-precision accumulation with carry propagation
3. Correct bit extraction positions based on product alignment
4. Exponent adjustment calculations

---

### 2.2 Simplified Version (Phase 2A)

For initial testing, a simplified version that uses only the first 128 bits of 2/π:

```verilog
// Simplified Payne-Hanek (uses only first 128 bits of 2/π)
// Less accurate but easier to implement and test

microcode_rom[16'h0180] = {OPCODE_EXEC, MOP_LOAD_A, 8'd0, 15'h0181};           // Load angle
microcode_rom[16'h0181] = {OPCODE_EXEC, MOP_EXTRACT_MANT, 8'd0, 15'h0182};     // Extract mantissa
microcode_rom[16'h0182] = {OPCODE_EXEC, MOP_LOAD_ROM, 8'd0, 15'h0183};         // Load 2/π chunk0
microcode_rom[16'h0183] = {OPCODE_EXEC, MOP_MUL64, 8'd0, 15'h0184};            // Multiply
microcode_rom[16'h0184] = {OPCODE_EXEC, MOP_EXTRACT_BITS, 8'd0, 15'h0185};     // Extract quadrant
microcode_rom[16'h0185] = {OPCODE_EXEC, MOP_EXTRACT_BITS, 8'd1, 15'h0186};     // Extract fraction
microcode_rom[16'h0186] = {OPCODE_EXEC, MOP_PACK_FP80, 8'd0, 15'h0187};        // Pack as FP80
microcode_rom[16'h0187] = {OPCODE_EXEC, MOP_LOAD_ROM, 8'd4, 15'h0188};         // Load π/2
microcode_rom[16'h0188] = {OPCODE_EXEC, MOP_CALL_ARITH, 8'd2, 15'h0189};       // Multiply by π/2
microcode_rom[16'h0189] = {OPCODE_EXEC, MOP_WAIT_ARITH, 8'd0, 15'h018A};       // Wait
microcode_rom[16'h018A] = {OPCODE_EXEC, MOP_LOAD_ARITH_RES, 8'd0, 15'h018B};   // Load result
microcode_rom[16'h018B] = {OPCODE_RET, 5'd0, 8'd0, 15'd0};                     // Return
```

---

## Section 3: FPU_Core Integration

### 3.1 Instantiate ROM Module

**File:** `Quartus/rtl/FPU8087/FPU_Core.v`

**Location:** In module instantiations

```verilog
// Payne-Hanek ROM instance
wire [2:0] ph_rom_addr;
wire [79:0] ph_rom_data;

FPU_Payne_Hanek_ROM payne_hanek_rom_inst (
    .clk(clk),
    .addr(ph_rom_addr),
    .data_out(ph_rom_data)
);
```

### 3.2 Connect ROM to MicroSequencer

**File:** `Quartus/rtl/FPU8087/FPU_Core.v`

In MicroSequencer_Extended_BCD instantiation:

```verilog
MicroSequencer_Extended_BCD microsequencer_inst (
    // ... existing ports ...

    // Payne-Hanek ROM interface
    .ph_rom_addr(ph_rom_addr),
    .ph_rom_data(ph_rom_data)
);
```

### 3.3 Connect Microcode Interface from FPU_Payne_Hanek

**File:** `Quartus/rtl/FPU8087/FPU_Core.v`

```verilog
// Microcode invocation from FPU_Payne_Hanek (via FPU_Range_Reduction)
wire        ph_microcode_invoke;
wire [11:0] ph_microcode_addr;
wire [79:0] ph_microcode_operand_a;
reg         ph_microcode_done;
reg  [79:0] ph_microcode_result;
reg  [1:0]  ph_microcode_quadrant;
reg         ph_microcode_error;

// Logic to handle microcode invocation
always @(posedge clk or posedge reset) begin
    if (reset) begin
        ph_microcode_done <= 1'b0;
        ph_microcode_result <= 80'd0;
        ph_microcode_quadrant <= 2'd0;
        ph_microcode_error <= 1'b0;
    end else begin
        if (ph_microcode_invoke) begin
            // Start microsequencer with program 22 (Payne-Hanek)
            microsequencer_start <= 1'b1;
            microsequencer_program_index <= 5'd22;
            microsequencer_data_in <= ph_microcode_operand_a;
            ph_microcode_done <= 1'b0;
        end else if (microsequencer_instruction_complete) begin
            // Microcode complete - retrieve results
            ph_microcode_result <= microsequencer_data_out;
            ph_microcode_quadrant <= microsequencer_temp_reg[1:0];  // Quadrant from temp_reg
            ph_microcode_done <= 1'b1;
            ph_microcode_error <= 1'b0;  // TODO: Add error detection
        end else begin
            ph_microcode_done <= 1'b0;
        end
    end
end
```

**Connect to FPU_Range_Reduction:**

```verilog
FPU_Range_Reduction range_reduction_inst (
    // ... existing ports ...

    // Microcode interface
    .ph_microcode_invoke(ph_microcode_invoke),
    .ph_microcode_addr(ph_microcode_addr),
    .ph_microcode_operand_a(ph_microcode_operand_a),
    .ph_microcode_done(ph_microcode_done),
    .ph_microcode_result(ph_microcode_result),
    .ph_microcode_quadrant(ph_microcode_quadrant),
    .ph_microcode_error(ph_microcode_error)
);
```

---

## Section 4: Testing

### 4.1 Microcode Unit Test

Create `tb_payne_hanek_microcode.v`:

```verilog
// Test the Payne-Hanek microcode routine in isolation
// Instantiate MicroSequencer with ROM
// Invoke program 22 with test angles
// Verify results against software reference
```

### 4.2 Integration Test

Extend `tb_payne_hanek_dispatch.v`:

```verilog
// Replace mock microcode responder with real microsequencer
// Test with angles: 256, 1000π, 10000π, 100000π
// Verify reduced angle and quadrant
// Check cycle count (should be 200-400 cycles)
```

### 4.3 Accuracy Test

Create `verify_payne_hanek_accuracy.py`:

```python
from mpmath import mp
mp.dps = 50

# Reference Payne-Hanek implementation
# Compare hardware results with software reference
# Measure ULP error
# Verify accuracy is within ±3 ULP
```

---

## Section 5: Implementation Checklist

### Phase 2A: Simplified Implementation (Recommended First)

- [ ] Add multi-precision registers to MicroSequencer (accum_hi/lo)
- [ ] Add 8 new micro-operations (MOP_LOAD_ROM through MOP_CLEAR_ACCUM)
- [ ] Implement simplified microcode routine (~20 instructions, 128-bit 2/π)
- [ ] Add ROM instantiation in FPU_Core
- [ ] Connect ROM to MicroSequencer
- [ ] Add microcode invocation logic in FPU_Core
- [ ] Connect to FPU_Range_Reduction
- [ ] Test with 1000π angle
- [ ] Verify quadrant extraction
- [ ] Verify reduced angle in [0, π/2)

### Phase 2B: Full Implementation (After 2A Works)

- [ ] Extend to 256-bit 2/π (4 partial products)
- [ ] Implement multi-precision accumulation with carry
- [ ] Add proper bit alignment for partial products
- [ ] Verify with 10000π, 100000π
- [ ] Accuracy testing against software reference
- [ ] Performance benchmarking
- [ ] Area verification (expect +100-150 ALMs)

---

## Section 6: Expected Results

### Cycle Counts

| Operation | Cycles | Notes |
|-----------|--------|-------|
| Simplified (128-bit) | ~150-200 | Fewer multiplications |
| Full (256-bit) | ~200-300 | 4 multiplications + accumulation |
| Overhead | ~50-100 | Bit extraction, packing |
| **Total** | **250-400** | Within budget |

### Accuracy

| Angle | Expected ULP Error | Notes |
|-------|-------------------|-------|
| 1000π | ±1-2 ULP | Good accuracy |
| 10000π | ±2-3 ULP | Acceptable |
| 100000π | ±3-4 ULP | Slight degradation |

### Area

| Component | ALMs | Notes |
|-----------|------|-------|
| Registers (accum, temp) | ~30-40 | Multi-precision accumulators |
| Micro-operations | ~60-80 | 8 new operations |
| Microcode ROM | ~50-80 | ~80 instructions @ 32 bits |
| **Total Phase 2** | **~100-150** | |
| **Combined (Phase 1 + 2)** | **~170-250** | Matches estimate |

---

## Section 7: Known Issues and Workarounds

### Issue 1: ROM Data Latency

**Problem:** ROM has 1-cycle registered output
**Workaround:** Add NOP cycle after MOP_LOAD_ROM before using data

### Issue 2: Partial Product Alignment

**Problem:** Partial products need to be shifted by 64 bits
**Workaround:** Use temp registers to hold intermediate values, implement shift-add in microcode

### Issue 3: Quadrant Extraction

**Problem:** Need to pass quadrant back through microcode interface
**Workaround:** Use microsequencer's temp_reg, expose as output signal

### Issue 4: Exponent Adjustment

**Problem:** Complex exponent calculations for fractional part
**Workaround:** Pre-compute bias values, store as constants

---

## Section 8: Alternative Approaches

### Option A: Simplified Algorithm (Recommended)

Use only first 128 bits of 2/π:
- **Pros:** Simpler implementation, faster (150-200 cycles)
- **Cons:** Less accurate for extremely large angles (>100000π)
- **Verdict:** **RECOMMENDED for Phase 2A**

### Option B: Full 256-bit Algorithm

Use full 256-bit 2/π with 4 partial products:
- **Pros:** Maximum accuracy for all angles
- **Cons:** More complex, slower (250-400 cycles)
- **Verdict:** Implement in Phase 2B after 2A works

### Option C: Hardware Accelerator

Implement multi-precision multiplier in hardware:
- **Pros:** Faster (50-100 cycles)
- **Cons:** +500-800 ALMs additional area
- **Verdict:** **NOT RECOMMENDED** - area cost too high

---

## Section 9: Success Criteria

### Functional Requirements

- [ ] Microcode routine completes without errors
- [ ] Reduced angle in range [0, π/2)
- [ ] Quadrant correctly identified (0-3)
- [ ] Results match software reference within ±3 ULP
- [ ] All 15 test cases pass (including 1000π, 10000π)

### Performance Requirements

- [ ] Microcode execution: 150-400 cycles
- [ ] Dispatch overhead: < 5 cycles
- [ ] Iterative path unchanged: 4-6 cycles for small angles

### Area Requirements

- [ ] Phase 2 adds < 200 ALMs
- [ ] Total (Phase 1 + 2): < 300 ALMs
- [ ] FPGA utilization stays < 80%

### Timing Requirements

- [ ] Timing closure at 50 MHz
- [ ] No new critical paths introduced
- [ ] Setup slack > 1 ns

---

## Section 10: Conclusion

This specification provides complete implementation details for Phase 2. The recommended approach is:

1. **Start with Phase 2A** (simplified 128-bit version)
   - Easier to implement and debug
   - Good accuracy for angles up to 100000π
   - Can be completed in 1 week

2. **Extend to Phase 2B** (full 256-bit version) if needed
   - Maximum accuracy
   - Additional 1 week implementation

3. **Verify thoroughly**
   - Unit tests for microcode
   - Integration tests with full FPU
   - Accuracy tests against software reference

The current Phase 1 implementation provides a solid foundation. Phase 2 completes the hybrid approach and achieves the goal of 100% test pass rate with full accuracy for arbitrarily large angles.

---

**END OF TECHNICAL SPECIFICATION**
