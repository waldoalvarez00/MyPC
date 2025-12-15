# FWAIT Implementation Analysis: Hardware Stall vs. Microcode Polling

**Date**: 2025-11-12
**Session**: claude/fpu-partial-connection-011CV3B5QfVtpNpWFAy1Eoyp

---

## Executive Summary

This document evaluates two approaches for implementing the FWAIT (WAIT) instruction to synchronize CPU and FPU operations:

1. **Current Approach**: Hardware stall in Core.sv
2. **Alternative Approach**: Microcode polling loop

**Recommendation**: **Microcode polling** is superior for this architecture.

---

## Approach 1: Hardware Stall (Current Implementation)

### Implementation

**Core.sv (Line 239)**:
```systemverilog
wire fwait_stall = (opcode == 8'h9B) && fpu_busy;
wire do_stall = loadstore_busy | divide_busy | alu_busy | fwait_stall;
```

**Microcode (wait.us)**:
```
.at 0x9b;
    next_instruction;
```

### How It Works
1. CPU fetches FWAIT instruction (opcode 0x9B)
2. Microcode executes `next_instruction`
3. Hardware detects `opcode == 8'h9B` in Core.sv
4. If `fpu_busy = 1`, `fwait_stall` asserts
5. `do_stall` prevents microcode sequencer from advancing
6. Pipeline stalls until `fpu_busy = 0`
7. Microcode proceeds to next instruction

### Advantages ✅
- **Simple microcode**: Just 1 instruction (`next_instruction`)
- **Zero microcode cycles**: Stall happens in hardware, not visible to microcode
- **Clean separation**: Hardware handles synchronization
- **Low overhead**: No microcode ROM space used for polling loop

### Disadvantages ❌
- **Opaque behavior**: Wait happens invisibly to microcode
- **Less flexible**: Cannot add exception checks during wait
- **Pipeline stall**: Entire microcode engine frozen
- **Hidden state**: Debugging harder (stall not in microcode trace)
- **Architectural mismatch**: Real 8087 uses explicit polling via BUSY# pin

---

## Approach 2: Microcode Polling (Proposed)

### Implementation Required

#### 1. Add New Jump Type

**utils/microassembler/uasm.py** (Add to enums):
```python
class JumpType(Enum):
    # ... existing types ...
    FPU_BUSY = 10  # New jump type
```

**utils/microassembler/uasm.py** (Line ~410):
```python
microcode_fields = {
    # ... existing fields ...
    'jmp_if_fpu_busy': (0, partial(_jump, jump_type=JumpType.FPU_BUSY), False),
}
```

#### 2. Update Microcode Types

**Quartus/rtl/CPU/MicrocodeTypes.sv** (Line 79-90):
```systemverilog
typedef enum bit [3:0] {
    JumpType_UNCONDITIONAL = 4'd0,
    // ... existing types ...
    JumpType_LOOP_DONE = 4'd9,
    JumpType_FPU_BUSY = 4'd10  // New type
} MC_JumpType_t;
```

#### 3. Wire FPU Busy to Microcode Module

**Quartus/rtl/CPU/Core.sv** (Add to Microcode instantiation):
```systemverilog
Microcode Microcode(
    .clk(sys_clk),
    .reset(reset),
    // ... existing ports ...
    .fpu_busy(fpu_busy),  // NEW: Wire FPU busy signal
    // ... rest of ports ...
);
```

**Quartus/rtl/CPU/InstructionDefinitions.sv** (Add module port):
```systemverilog
module Microcode(
    input logic clk,
    input logic reset,
    // ... existing ports ...
    input logic fpu_busy,  // NEW: FPU busy input
    // ... rest of ports ...
);
```

#### 4. Implement Jump Logic

**Quartus/rtl/CPU/InstructionDefinitions.sv** (In jump_target case statement):
```systemverilog
unique case (current.jump_type)
    JumpType_RM_REG_MEM: jump_target = current.next + {{addr_bits-1{1'b0}}, ~rm_is_reg};
    // ... existing cases ...
    JumpType_FPU_BUSY: jump_target = fpu_busy ? current.next : addr + 1'b1;  // NEW
    default: jump_target = current.next;
endcase
```

#### 5. Update FWAIT Microcode

**utils/microassembler/microcode/wait.us**:
```
.at 0x9b;
    jmp do_fwait;

.auto_address;
do_fwait:
    // Poll FPU busy signal
    // If busy: jump back to do_fwait (current.next points to itself)
    // If not busy: proceed to next microcode address (addr + 1)
    jmp_if_fpu_busy do_fwait;

    // FPU ready - continue to next instruction
    next_instruction;
```

### How It Works
1. CPU fetches FWAIT instruction (opcode 0x9B)
2. Microcode jumps to `do_fwait` label
3. Microcode executes `jmp_if_fpu_busy do_fwait`
4. Hardware checks `fpu_busy` signal
5. If `fpu_busy = 1`: jump back to `do_fwait` (polling loop)
6. If `fpu_busy = 0`: proceed to `next_instruction`
7. CPU continues to next x86 instruction

### Advantages ✅
- **Visible behavior**: Wait loop explicit in microcode
- **Flexible**: Can add exception checks in polling loop
- **Debuggable**: Microcode trace shows polling iterations
- **Architecturally accurate**: Matches 8087 BUSY# pin polling
- **Extensible**: Easy to add timeout or exception handling
- **Consistent**: Uses same conditional jump mechanism as other waits (REP loops, etc.)

### Disadvantages ❌
- **More microcode**: Uses 2-3 microcode ROM entries
- **Microcode overhead**: Each poll iteration = 1 microcode cycle
- **Requires changes**: Need to modify multiple files (assembler, types, hardware)
- **Jump overhead**: Small performance cost per poll iteration (~1-2 cycles)

---

## Performance Comparison

### Scenario: FPU Busy for 20 Cycles

#### Hardware Stall:
```
Cycle 0: FWAIT fetched, opcode decoded
Cycle 1: Microcode executes next_instruction
Cycle 2: Hardware detects fwait_stall, pipeline frozen
Cycle 3-21: Pipeline stalled (do_stall = 1)
Cycle 22: fpu_busy clears, pipeline resumes
Total: 22 cycles, 1 microcode instruction
```

#### Microcode Polling:
```
Cycle 0: FWAIT fetched, opcode decoded
Cycle 1: Microcode jumps to do_fwait
Cycle 2: Execute jmp_if_fpu_busy, fpu_busy=1, jump to do_fwait
Cycle 3: Execute jmp_if_fpu_busy, fpu_busy=1, jump to do_fwait
...
Cycle 21: Execute jmp_if_fpu_busy, fpu_busy=1, jump to do_fwait
Cycle 22: Execute jmp_if_fpu_busy, fpu_busy=0, fall through
Cycle 23: Execute next_instruction
Total: 23 cycles, 20 microcode instructions
```

**Difference**: +1 cycle overhead (negligible)

---

## Real 8087 Hardware Behavior

The Intel 8087 coprocessor uses the **BUSY# pin** for synchronization:

```
8086 CPU: Executes FWAIT instruction
8086 CPU: Checks BUSY# pin
  If BUSY# = HIGH (active): Wait and check again (polling)
  If BUSY# = LOW (inactive): Continue to next instruction
```

**Microcode polling** more accurately reflects this hardware behavior.

---

## Extension Possibilities

With microcode polling, we can easily add features:

### Exception Checking
```
do_fwait:
    jmp_if_fpu_int do_fpu_exception;  // Check FPU interrupt
    jmp_if_fpu_busy do_fwait;         // Poll busy
    next_instruction;
```

### Timeout (Prevent Infinite Loop)
```
do_fwait:
    // Decrement timeout counter
    a_sel TMP, b_sel IMMEDIATE, immediate 0x1, alu_op SUB, tmp_wr_en;

    // Check if timeout expired
    jmp_if_zero do_fwait_timeout;

    // Continue polling
    jmp_if_fpu_busy do_fwait;
    next_instruction;

do_fwait_timeout:
    // Generate exception for hung FPU
    b_sel IMMEDIATE, immediate 0x10, alu_op SELB, tmp_wr_en, jmp do_int;
```

### Debug Tracing
With microcode polling, each iteration is visible in microcode trace logs, making debugging much easier.

---

## Code Size Impact

### Current Approach:
- **Microcode ROM**: 1 entry (0x9B → next_instruction)
- **Hardware**: 1 additional wire in Core.sv

### Polling Approach:
- **Microcode ROM**: 3-4 entries (jump label + conditional jump + next_instruction)
- **Hardware**:
  - 1 new jump type enum value
  - 1 case in jump_target logic
  - 1 wire to Microcode module
  - ~10 lines of SystemVerilog

**ROM Impact**: +2-3 entries out of 1196 total = **+0.2% increase** (negligible)

---

## Recommendation: Microcode Polling

### Why Polling is Better:

1. **Architectural Accuracy**: Matches real 8087 BUSY# pin polling behavior
2. **Debuggability**: Visible in microcode trace, easier to debug
3. **Extensibility**: Easy to add exception handling, timeout, etc.
4. **Consistency**: Uses standard conditional jump mechanism
5. **Minimal Overhead**: Only 1 extra cycle, negligible impact

### Why Not Hardware Stall:

1. **Opaque**: Hidden behavior makes debugging harder
2. **Inflexible**: Cannot add features like exception checking
3. **Inconsistent**: Other waits (REP loops) use microcode polling
4. **Non-standard**: Doesn't match 8087 specification

---

## Implementation Steps for Polling Approach

### Phase 1: Assembler Changes
1. Add `JumpType.FPU_BUSY = 10` to uasm.py enums
2. Add `'jmp_if_fpu_busy'` to microcode_fields dictionary
3. Test microcode build

### Phase 2: Type Definitions
1. Add `JumpType_FPU_BUSY = 4'd10` to MicrocodeTypes.sv
2. Update `MC_JumpType_t_BITS` if needed (currently 4 bits supports up to 15)

### Phase 3: Hardware Integration
1. Add `input logic fpu_busy` to Microcode module port list
2. Add case `JumpType_FPU_BUSY` to jump_target logic
3. Wire `fpu_busy` from Core to Microcode module

### Phase 4: Microcode Update
1. Update wait.us with polling loop
2. Remove `fwait_stall` logic from Core.sv (no longer needed)
3. Rebuild microcode ROM

### Phase 5: Testing
1. Test microcode build (should compile successfully)
2. Test in simulation (verify polling behavior)
3. Synthesize and test on FPGA

**Estimated Effort**: 2-3 hours of work

---

## Alternative: Hybrid Approach

If we want to keep current simplicity but add visibility, we could:

1. Keep hardware stall in Core.sv
2. Add microcode loop that checks a "stall occurred" flag
3. Log/trace when FWAIT stalls happened

**Not recommended**: Adds complexity without full benefits of polling.

---

## Conclusion

**Microcode polling is the superior approach** for implementing FWAIT:
- Better matches 8087 architecture
- Easier to debug and extend
- Minimal performance overhead
- Consistent with rest of microcode design

**Recommendation**: Implement microcode polling approach for production system.

---

## References

- Intel 8087 Datasheet: Section on BUSY# pin operation
- Intel 8086 Family User's Manual: WAIT instruction specification
- Current implementation: Core.sv lines 237-242
- Current microcode: wait.us lines 18-25
