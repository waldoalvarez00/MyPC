# FPU Microcode-Based Access Implementation Guide

**Date**: 2025-11-12
**Status**: Infrastructure Ready - Microcode Implementation Pending

---

## Overview

This document describes the authentic 8087-style FPU integration using microcode control signals instead of I/O ports. The hardware infrastructure is in place; microcode implementation is pending.

## Current Status

### ✅ Completed Hardware Infrastructure

1. **FPU Status Word Wiring**
   - FPU status word connected from FPU8087 → Top.sv → Core.sv
   - Available as `fpu_status_word[15:0]` input in Core.sv:62
   - Real-time visibility of FPU status

2. **FPU Memory Interface**
   - FPU can read/write memory directly for memory operands
   - Connected to CPU memory arbiter
   - Handles: FILD [mem], FST [mem], FADD [mem], etc.

3. **ESC Instruction Detection**
   - CPU detects ESC instructions (0xD8-0xDF)
   - Signals FPU with opcode and ModR/M byte
   - FWAIT synchronization working

4. **Removed Non-Authentic I/O Port Interface**
   - FPU_IO_Port removed from active integration
   - Kept in source tree for reference: `Quartus/rtl/FPU8087/FPU_IO_Port.sv`

### ⚠️ Pending: Microcode Implementation

Requires microcode format changes and rebuild via `uasm.py`

---

## Real 8087 Data Flow

### Memory Operands (Already Working ✅)
Most FPU instructions use memory operands:

```
FILD [BX]     ; FPU reads from memory address in BX
FST [SI+4]    ; FPU writes to memory address SI+4
FADD [mem]    ; FPU reads operand from memory
```

**Current Implementation**: Works! FPU uses its memory interface.

### Register Operands (Already Working ✅)
Stack-based operations stay within FPU:

```
FADD ST(0), ST(1)   ; All in FPU stack
FMUL ST(2), ST(0)   ; All in FPU stack
FXCH ST(3)          ; Exchange within FPU
```

**Current Implementation**: Works! FPU handles internally.

### Special Case: FSTSW AX (Needs Microcode)
The ONLY instruction that requires direct CPU-FPU data transfer:

```
FSTSW AX      ; Encoding: 9B DF E0 (or just DF E0)
              ; Store FPU status word in AX register
```

**Current Implementation**: Needs microcode support (see below).

---

## Required Microcode Changes

### Option 1: Add FPU Status to A-Bus (Requires Format Change)

**Changes Needed**:

1. **Expand ADriver enum** (`MicrocodeTypes.sv`):
   ```systemverilog
   typedef enum bit [2:0] {  // Changed from [1:0] to [2:0]
       ADriver_RA = 3'd0,
       ADriver_IP = 3'd1,
       ADriver_MAR = 3'd2,
       ADriver_MDR = 3'd3,
       ADriver_FPU_STATUS = 3'd4  // NEW!
   } MC_ADriver_t;
   `define MC_ADriver_t_BITS 3  // Changed from 2 to 3
   ```

2. **Update A-bus mux** (`Core.sv:69-72`):
   ```systemverilog
   wire [15:0] a_bus =
       a_sel == ADriver_RA ? reg_rd_val[0] :
       a_sel == ADriver_IP ? ip_current :
       a_sel == ADriver_MAR ? mar :
       a_sel == ADriver_FPU_STATUS ? fpu_status_word :  // NEW!
       mdr;
   ```

3. **Create microcode** (`utils/microassembler/microcode/fstsw_ax.us`):
   ```
   // FSTSW AX - DF E0
   // Store FPU status word in AX register

   .at 0xdf;
       jmp_rm_reg do_fstsw_reg, do_esc;

   .auto_address;
   do_fstsw_reg:
       // Check if this is FSTSW AX (ModR/M = E0)
       // If modrm_reg == 0 (bits 5:3), it's FSTSW
       // Read FPU status word to A-bus, write to AX
       a_sel FPU_STATUS, alu_op SELA;
       rd_sel AX, reg_wr_en;
       next_instruction;
   ```

4. **Rebuild microcode**:
   ```bash
   cd utils/microassembler/
   python uasm.py -o ../../Quartus/rtl/CPU/InstructionDefinitions.sv microcode/*.us
   ```

**Impact**: Microcode format changes from 95 bits to 96 bits.

---

### Option 2: Load Status to MDR (Minimal Format Change)

**Changes Needed**:

1. **Add microcode field** (`MicrocodeTypes.sv` - in microcode record):
   ```systemverilog
   logic fpu_status_to_mdr;  // 1 bit - load FPU status into MDR
   ```

2. **Add MDR load logic** (`Core.sv` - in MDR write section):
   ```systemverilog
   // MDR write logic
   always_ff @(posedge clk) begin
       if (fpu_status_to_mdr)
           mdr <= fpu_status_word;
       else if (mdr_write)
           mdr <= /* existing logic */;
   end
   ```

3. **Create microcode** (`utils/microassembler/microcode/fstsw_ax.us`):
   ```
   // FSTSW AX - DF E0
   .at 0xdf;
       jmp_rm_reg do_fstsw_reg, do_esc;

   .auto_address;
   do_fstsw_reg:
       // Load FPU status into MDR
       fpu_status_to_mdr;

       // Read MDR to A-bus, write to AX
       a_sel MDR, alu_op SELA;
       rd_sel AX, reg_wr_en;
       next_instruction;
   ```

4. **Rebuild microcode** (same as above).

**Impact**: Adds 1 bit to microcode format (95 → 96 bits).

---

## Microcode Assembler Notes

**Known Issue**: The microcode assembler (`uasm.py`) had errors in previous sessions:
```
AttributeError: 'str' object has no attribute 'lines'
```

**Location**: Line 140 in `uasm.py` - preprocessor output parsing

**Before Implementing**: Fix the assembler issue or verify it works with current microcode.

---

## Testing Plan

### Phase 1: Verify Existing Functionality
```bash
cd modelsim/
./run_fpu_interface_simple_test.sh  # Should pass
```

### Phase 2: Test FSTSW AX (After Microcode Changes)

Create testbench: `modelsim/tb_fstsw_ax.sv`

```systemverilog
// Pseudo-code test
initial begin
    // Setup: FPU has status word 0x3800

    // Execute: FSTSW AX (DF E0)
    execute_instruction(8'hDF, 8'hE0);

    // Verify: AX contains 0x3800
    assert(ax_register == 16'h3800);
end
```

---

## Alternative: FSTSW to Memory (Already Works!)

**Good News**: FSTSW with memory operands already works via FPU memory interface:

```
FSTSW [status_var]    ; DF /7 - Works today!
MOV AX, [status_var]  ; Then read to AX
```

This is a **valid workaround** until microcode support is added.

---

## Implementation Priority

### High Priority (Authentic 8087)
- [ ] Fix microcode assembler if broken
- [ ] Implement Option 2 (minimal change)
- [ ] Test FSTSW AX instruction
- [ ] Document any remaining issues

### Low Priority (Extended Features)
- [ ] FLDCW direct (memory version works)
- [ ] FSTCW direct (memory version works)
- [ ] FPU exception INT routing (currently tied off)

---

## Current FPU Integration Status

| Feature | Status | Notes |
|---------|--------|-------|
| ESC instruction detection | ✅ Working | Core.sv:112 |
| FPU receives opcode/modrm | ✅ Working | Direct signals |
| FWAIT synchronization | ✅ Working | Polls fpu_busy |
| FPU memory access | ✅ Working | Via arbiter |
| Memory operands | ✅ Working | FILD/FST/FADD [mem] |
| Register operands | ✅ Working | All stack ops |
| FSTSW [mem] | ✅ Working | Via memory interface |
| FSTSW AX | ⚠️ Needs microcode | This document |
| FLDCW [mem] | ✅ Working | Via memory interface |
| FSTCW [mem] | ✅ Working | Via memory interface |
| FPU exceptions | ⚠️ Partial | Signal exists, not routed |

---

## Files Modified

- `Quartus/rtl/common/Top.sv` - Removed I/O port, wired status word
- `Quartus/rtl/CPU/Core.sv` - Added fpu_status_word input
- `Quartus/rtl/CPU/Microcode.sv` - Already has fpu_busy for FWAIT
- `docs/FPU_MICROCODE_ACCESS_IMPLEMENTATION.md` - This file

## Files Pending Changes

- `Quartus/rtl/CPU/MicrocodeTypes.sv` - Add ADriver_FPU_STATUS or fpu_status_to_mdr
- `utils/microassembler/microcode/fstsw_ax.us` - New file
- `Quartus/rtl/CPU/InstructionDefinitions.sv` - Regenerated from microcode

---

## Conclusion

The hardware infrastructure for authentic 8087 microcode-based access is **complete**. The FPU can handle all standard operations. Only FSTSW AX requires microcode changes, which involves:

1. Fixing/verifying the microcode assembler
2. Adding 1 new microcode field or expanding ADriver
3. Writing ~5 lines of microcode
4. Rebuilding

**Workaround**: Use `FSTSW [mem]` + `MOV AX, [mem]` until microcode is updated.

The current implementation is **authentic 8087** except for this one special case.
