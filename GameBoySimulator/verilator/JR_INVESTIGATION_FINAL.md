# JR Instruction Investigation - Final Report
## Date: 2025-12-11

## Summary

The TV80 GameBoy core has **MULTIPLE bugs** related to JR (relative jump) instructions. My initial fix addressed one bug but exposed/worsened another.

## Bugs Identified

### Bug #1: Unconditional JR (0x18) - PC Increments Byte-by-Byte

**Test**: `JR +2` from $0160 (should jump to $0164)

**Original TV80 Behavior**: ❌ FAIL
- PC progression: $0160 → $0161 → $0162 → (stops at HALT)
- Does NOT jump - executes byte-by-byte through instruction bytes

**With My Fix** (`PC16_B = offset - 1`): ✅ PASS
- PC progression: $0160 → $0161 → $0162 (M3) → $0163 → ...
- Successfully jumps to target!

**Root Cause**: PC auto-increments twice:
1. M1 T3 (line 463): Automatic increment
2. M2 T3 (line 691): Inc_PC microcode
3. M3 starts with PC already 1 too high

### Bug #2: Conditional JR When FALSE - Jumps When It Shouldn't

**Test**: `JR C, +5` when carry is CLEAR (should NOT jump)

**Original TV80 Behavior**: ❌ FAIL
- PC progression: $0151 → $0152 → $0153 → $0158
- Jumps by offset (+5) even though condition is FALSE!

**With My Fix**: ❌ WORSE
- PC progression: $0151 → $0152 → $0153 → $0157
- Still jumps, but by offset - 1 (+4 instead of +5)

**Root Cause**: TV80 conditional JR microcode logic seems backwards:

```verilog
// From tv80_mcode.v lines 1333-1338
case (IR[4:3])
  3 : MCycles = (F[Flag_C]) ? 3'd2 : 3'd3;   // JR C
endcase

// M3 always has:
MCycle[2] :
  begin
    NoRead = 1'b1;
    JumpE = 1'b1;  // ← ALWAYS asserts jump!
    TStates = 3'd5;
  end
```

**The Issue**:
- Condition TRUE → MCycles = 2 (M1, M2 only, no M3)
- Condition FALSE → MCycles = 3 (M3 executes with JumpE = 1)

This means:
- When condition is TRUE (should jump): No M3, no JumpE! How does it jump?
- When condition is FALSE (should NOT jump): M3 with JumpE = 1 executes! It jumps!

**This appears to be a fundamental flaw in the TV80 conditional JR implementation.**

## Z80 vs TV80 Behavior

### Z80 Specification:
- JR condition TRUE: 12 T-states (3 M-cycles), JUMP
- JR condition FALSE: 7 T-states (2 M-cycles), NO JUMP

### TV80 Implementation:
- Condition TRUE: MCycles = 2, NO M3 (no JumpE)
- Condition FALSE: MCycles = 3, M3 with JumpE = 1

**TV80's logic appears backwards or incomplete!**

## Why My Fix Broke Conditional JR

My fix: `PC16_B = offset - 1` when `JumpE = 1`

This works for unconditional JR (0x18) but makes conditional JR worse because:
1. When condition is FALSE, M3 still executes with JumpE = 1
2. My fix subtracts 1 from the offset
3. It jumps by offset - 1 instead of not jumping at all

## Solution Options

### Option 1: Two-Part Fix ⚠️ COMPLEX
1. Fix unconditional JR (0x18) with -1 compensation
2. Fix conditional JR microcode to NOT assert JumpE when condition is FALSE
   - Requires understanding how condition TRUE case jumps without JumpE

### Option 2: Investigate 2-Cycle Jump Mechanism ⏳ RESEARCH NEEDED
- When MCycles = 2 (condition TRUE), how does the jump happen?
- Maybe PC gets updated differently at instruction end?
- Need to trace through TV80 state machine more carefully

### Option 3: Rewrite Conditional JR Logic ⚠️ RISKY
- Change microcode to match Z80 behavior correctly
- Condition TRUE → 3 MCycles with JumpE
- Condition FALSE → 2 MCycles, end early

### Option 4: Use IR-Specific Fix ⭐ RECOMMENDED
- Add IR to PC16_B sensitivity list
- Only apply -1 for unconditional JR: `if (JumpE && IR == 8'h18)`
- Leave conditional JR broken for now (separate issue)

## Current Status

### Working ✅
- JP (absolute jump) - No regression
- Regular instructions (LD, ADD, NOP, etc.) - No regression

### Partially Working ⚠️
- JR (unconditional) - Works with my fix, broken without it

### Broken ❌
- JR C / JR NC / JR Z / JR NZ when condition is FALSE - Broken in original TV80, worse with my fix

## Recommendation

**Apply targeted fix for unconditional JR only**, document conditional JR as a known TV80 core bug:

```verilog
// Add IR to sensitivity list
always @(/*AUTOSENSE*/BTR_r or DI_Reg or IncDec_16 or JumpE or PC
         or RegBusA or RegBusC or SP or tstate or IR)
  begin
    if (JumpE == 1'b1 )
      begin
        // Only apply -1 compensation for unconditional JR (0x18)
        // Conditional JR has separate bugs that need different fix
        if (IR == 8'h18)
          PC16_B = { {8{DI_Reg[7]}}, DI_Reg } - 1;
        else
          PC16_B = { {8{DI_Reg[7]}}, DI_Reg };
      end
    // ...
```

## Game Impact

- Game ROM has 1,586 JR instructions
- Unknown how many are unconditional vs conditional
- Conditional JR bugs will prevent game from running correctly
- **This is a critical issue that requires further investigation**

## Next Steps

1. Apply targeted fix for unconditional JR (0x18)
2. Test with game ROM to see how many conditional JR failures occur
3. Research TV80 2-cycle jump mechanism
4. Consider alternative CPU cores if TV80 bugs are too severe

---

**Priority**: 🚨 CRITICAL
**Status**: PARTIALLY RESOLVED - Unconditional JR fixed, conditional JR still broken
**Blocker**: Conditional JR bugs in original TV80 core
