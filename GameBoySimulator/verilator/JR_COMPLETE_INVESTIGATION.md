# JR Instruction - Complete Investigation Report
## Date: 2025-12-11

## Summary

The TV80 GameBoy core has **CRITICAL BUGS** in JR (relative jump) instruction implementation that prevent games from running. Multiple attempted fixes have failed.

## The Problems

### Problem #1: Unconditional JR (0x18) Doesn't Jump

**Test Case**: `JR +2` from $0160 (should jump to $0164)

**Observed Behavior**:
- PC progression: $0160 → $0161 → $0162 (HALT)
- Does NOT jump - treats each byte as separate instruction
- MCycle progression: M1 → M2 → M3, then M1 for next byte

**Root Cause Analysis**:
- M1 T3 (line 463 in tv80_core.v): PC auto-increments to fetch next byte
- M2 T3 (line 691): Inc_PC microcode increments PC again
- By M3, PC is already 1 byte too far ahead
- When JumpE asserts in M3, PC calculation is off by 1

### Problem #2: Conditional JR - Microcode Logic Backwards

**Test Case**: `JR C, +5` when carry is CLEAR (should NOT jump)

**Observed Behavior**:
- Jumps when it shouldn't!
- With offset compensation: jumps by offset-1
- Without compensation: jumps by full offset

**Root Cause** (tv80_mcode.v lines 1333-1338):
```verilog
case (IR[4:3])
  3 : MCycles = (F[Flag_C]) ? 3'd2 : 3'd3;   // JR C
endcase

MCycle[2] :  // M3
  begin
    NoRead = 1'b1;
    JumpE = 1'b1;  // ← ALWAYS asserts jump!
    TStates = 3'd5;
  end
```

**The Issue**:
- Condition TRUE → MCycles = 2 (no M3, no JumpE executed)
- Condition FALSE → MCycles = 3 (M3 executes with JumpE = 1)

This is **backwards**! When condition is FALSE, it should skip M3, not execute it.

### Problem #3: IR Register Doesn't Contain Opcode

**Critical Discovery**: The IR (Instruction Register) in TV80 does NOT hold the instruction opcode during execution!

**Evidence from test_ir_every_cycle.cpp**:
```
ROM: $0152 = 0x18 (JR opcode)
Actual: PC=$0152, IR=$01 (NOT $18!)
```

**Why This Matters**:
- Any fix that checks `if (IR == 8'h18)` will NEVER work
- IR contains internal state ($01, $02) not the opcode
- Cannot distinguish unconditional JR from other instructions via IR

## Attempted Fixes

### Fix #1: Global Offset Compensation ❌ FAILED
```verilog
PC16_B = { {8{DI_Reg[7]}}, DI_Reg } - 1;
```

**Applied to**: All JumpE cases
**Result**:
- Unconditional JR: Still fails (JR doesn't jump at all)
- Conditional JR: Makes it worse (jumps by wrong amount when it shouldn't jump)

### Fix #2: IR-Based Targeted Fix ❌ IMPOSSIBLE
```verilog
if (IR == 8'h18)
  PC16_B = { {8{DI_Reg[7]}}, DI_Reg } - 1;
```

**Applied to**: Only when IR equals JR opcode
**Result**: Never triggers because IR never contains 0x18!

### Why Fixes Don't Work

The problem is **deeper than offset calculation**. Evidence:

1. **JR doesn't execute M3 properly**: MCycle sequence shows M1 → M2 → M3, but then goes to M1 of next instruction instead of jumping

2. **JumpE may not be asserted**: The microcode might not be reaching the JumpE stage correctly

3. **PC increments independently**: Even with offset compensation, PC progresses linearly byte-by-byte

## Test Results Timeline

### Initial Tests (Before Any Fix)
- Unconditional JR (0x18): ❌ FAIL - increments byte-by-byte
- Conditional JR when TRUE: ❓ Unknown
- Conditional JR when FALSE: ❌ FAIL - jumps when it shouldn't

### After Global Fix (`PC16_B = offset - 1`)
- Unconditional JR: Some tests showed ✅ SUCCESS, others ❌ FAIL
- Conditional JR when FALSE: ❌ WORSE - jumps by wrong offset

### After IR-Based Fix
- Didn't change anything (IR never contains correct value)

### Current Status (Simple Fix Reapplied)
- Unconditional JR: ❌ FAIL - still doesn't jump
- IR values: $01 at JR location, never $18

## Technical Analysis

### MCycle Trace for Failed JR

```
Cycle 40686: PC=$0152 (JR location) IR=$01 MCycle=4 (M3) TState=2
Cycle 40846: PC=$0153 (offset byte)  IR=$01 MCycle=1 (M1) TState=2
Cycle 41070: PC=$0154 (should skip)  IR=$02 MCycle=1 (M1) TState=2
```

**Observations**:
1. At PC=$0152, we're in M3 (where JumpE should execute)
2. Next cycle shows PC=$0153 with MCycle=1 (new M1 cycle)
3. JR execution appears to complete, but no jump occurs
4. PC increments normally as if JR didn't exist

### Possible Root Causes

1. **JumpE Not Asserted**: Microcode might not be setting JumpE=1 in M3
2. **PC Calculation Ignored**: JumpE might be asserted but PC16_B addition not working
3. **Timing Issue**: PC update might happen before PC16_B is calculated
4. **GameBoy Mode Bug**: Mode 3 (LR35902) might have broken JR implementation

## Z80 vs TV80 Specifications

### Z80 Behavior (Correct):
- JR unconditional: 12 T-states, 3 M-cycles, JUMPS
- JR condition TRUE: 12 T-states, 3 M-cycles, JUMPS
- JR condition FALSE: 7 T-states, 2 M-cycles, NO JUMP

### TV80 Implementation (Broken):
- JR unconditional: Doesn't jump, increments byte-by-byte
- JR condition TRUE: MCycles = 2 (no M3, no JumpE)
- JR condition FALSE: MCycles = 3 (M3 with JumpE = 1), JUMPS

## Game Impact

The game ROM (`game.gb`) contains **1,586 JR instructions**. Current status:
- ❌ Unconditional JR: BROKEN - game cannot progress past first JR
- ❌ Conditional JR: BROKEN - logic errors will cause wrong behavior
- 🚨 **GAME CANNOT RUN** with current TV80 bugs

## Next Steps - Options

### Option 1: Deep TV80 Microcode Debug ⏰ Time-Consuming
- Add debug output for JumpE signal
- Trace PC16_B calculation during M3
- Check if PC16_B addition to PC actually happens
- May require days of debugging

### Option 2: Patch TV80 Microcode 🔧 Risky
- Modify tv80_mcode.v JR microcode sequences
- Fix conditional JR MCycles logic
- Ensure JumpE asserts correctly
- High risk of breaking other instructions

### Option 3: Alternative CPU Core 🔄 Major Work
- Replace TV80 with different GameBoy CPU core
- Options: SameBoy core, Gameboy-Online core, custom implementation
- Would require significant integration work
- But might be faster than fixing TV80

### Option 4: Report to TV80 Maintainers 📧 Long-Term
- Document all bugs found
- Submit to TV80 project (if still maintained)
- Wait for official fix
- Not viable for immediate project needs

## Recommendation

Given the depth and complexity of the TV80 bugs:

1. **Short-term**: Document JR as broken, work on other GameBoy features
2. **Medium-term**: Evaluate alternative CPU cores (SameBoy is well-tested)
3. **Long-term**: Consider contributing fixes back to TV80 project

The TV80 core has **fundamental microcode bugs** that cannot be fixed with simple PC calculation adjustments. A proper fix requires:
- Understanding TV80's complete microcode system
- Fixing both unconditional and conditional JR logic
- Ensuring no regressions in other jump instructions
- Extensive testing of all GameBoy instructions

**This is a project-blocking issue that needs a strategic decision on how to proceed.**

## Files Referenced

- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/tv80/rtl/core/tv80_core.v`
- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/tv80/rtl/core/tv80_mcode.v`
- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/JR_INVESTIGATION_FINAL.md`
- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/IR_REGISTER_INVESTIGATION.md`
- Test files: `test_jr_*.cpp`, `test_ir_*.cpp`, `test_carry_flag_debug.cpp`

## Test Commands

```bash
# Rebuild Verilator model
./verilate_gameboy.sh

# Test unconditional JR
g++ [compile flags] test_original_jr.cpp -o test_original_jr
./test_original_jr

# Detailed IR trace
g++ [compile flags] test_ir_timing.cpp -o test_ir_timing
./test_ir_timing
```

---

**Status**: 🚨 BLOCKED - JR instructions fundamentally broken in TV80 core
**Priority**: CRITICAL - Game cannot run without working JR
**Recommendation**: Evaluate alternative CPU cores or deep TV80 debugging
