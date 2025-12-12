# JR Instruction Root Cause Analysis - CRITICAL BUG FOUND
## Date: 2025-12-11

## EXECUTIVE SUMMARY

**ROOT CAUSE IDENTIFIED**: The TV80 core's IR (Instruction Register) is NOT being updated with newly fetched opcodes. When PC=$0150 (JR instruction), IR contains $C3 (previous JP instruction) instead of $18 (JR opcode).

**Impact**: The microcode `case (IR)` statement **NEVER matches JR** because IR never contains the JR opcode. This is why all JR instructions fail.

## The Smoking Gun

### Test Evidence

```
ROM Setup:
  $0150: 0x18 (JR opcode)
  $0151: 0x02 (offset)
  
Actual IR Content at PC=$0150:
  IR = $C3 (JP opcode from previous instruction at $0100!)
```

**Trace Output:**
```
Cycle    PC     IR
  541  $0150  $C3    [Should be $18!]
  542  $0150  $C3    [Still $C3]
  543  $0150  $C3    [Still $C3]
  ...
  590  $0150  $C3    [Never updates to $18]
```

### Why This Breaks JR

**Microcode Matching (tv80_mcode.v line 275):**
```verilog
casez (IR)
  8'b00011000 :  // Matches IR=$18 (JR) - NEVER HAPPENS!
    begin
      MCycles = 3'b011;  // This code NEVER executes
      case (1'b1)
        MCycle[2] :
          JumpE = 1'b1;  // Jump NEVER asserted
      endcase
    end
  
  8'b11000011 :  // Matches IR=$C3 (JP) - ALWAYS MATCHES!
    begin
      // Wrong microcode executes!
    end
endcase
```

**Result**: The microcode executes JP logic instead of JR logic, causing incorrect behavior.

## Why Some Instructions Work

**Hypothesis**: Instructions that work (LD, ADD, PUSH, etc.) might:
1. Have opcode patterns that happen to match even with stale IR values, OR
2. Be handled by default cases that don't strictly check IR, OR
3. Have IR updates that work correctly in some code paths but not others

**Needs Investigation**: Why does JP work if IR matching is broken?

## The Bigger Picture

### Previous Analysis Was Incomplete

**What We Fixed:**
- ✅ Conditional JR MCycles logic (backwards ternary operators)
- ✅ One test now passes (JR C when carry=0 - doesn't jump)

**What We Missed:**
- ❌ IR register not being updated with fetched opcode
- ❌ Microcode case matching fundamentally broken for JR
- ❌ Likely affects multiple instructions, not just JR

### Why Test 7 (JR C, carry=0) Passes

**Test 7**: JR C when carry=0 (should NOT jump)

**Why it passes:**
1. Condition is FALSE → MCycles = 2 (after our fix)
2. Only M1 and M2 execute, M3 (with JumpE) is skipped
3. **Doesn't matter that IR is wrong** - M3 never runs!
4. PC increments normally through M1/M2

**Why Tests 3, 6, 8 Still Fail**

**Test 3**: JR unconditional (should always jump)
**Test 6**: JR C when carry=1 (should jump)
**Test 8**: JR NC when carry=0 (should jump)

**Why they fail:**
1. MCycles = 3, so M3 should execute
2. But IR != $18, so microcode doesn't match JR case
3. JumpE never asserted
4. PC increments byte-by-byte instead of jumping

## The IR Update Problem

### Where IR Should Be Updated

In a correct Z80 implementation:
1. **M1 T2**: Opcode fetch from memory
2. **M1 T3**: Opcode loaded into IR
3. **M2+**: Microcode uses IR to control execution

### TV80 Implementation Issue

The IR register is clearly not being updated when PC advances to a new instruction. Possible causes:

1. **IR update gated by wrong condition** - Maybe only updates on certain instruction types
2. **Timing issue** - IR update happens too late or not at all
3. **Mode-specific bug** - GameBoy Mode 3 might have broken IR update
4. **Core architecture bug** - Fundamental flaw in TV80's fetch-decode

### Location to Investigate

**tv80_core.v** - Look for:
```verilog
IR <= ...;  // IR register update
// OR
assign IR = ...;  // IR assignment
```

Check conditions under which IR is updated.

## Proposed Fix Strategy

### Option 1: Fix IR Update Logic (CORRECT FIX)

**Difficulty**: Moderate to High
**Risk**: Medium (might break other instructions)
**Steps**:
1. Locate IR update logic in tv80_core.v
2. Verify it updates during M1 T3 for ALL instructions
3. Test with JR and other instructions
4. Ensure no regressions

### Option 2: Workaround - Decode from Memory (HACK)

**Difficulty**: High
**Risk**: Very High (major architectural change)
**Concept**:
- Modify tv80_mcode.v to check memory bus instead of IR
- Would break the whole microcode architecture
- NOT RECOMMENDED

### Option 3: Alternative CPU Core (NUCLEAR OPTION)

**Difficulty**: Extreme
**Risk**: Low (clean slate)
**Concept**:
- Replace TV80 with different GameBoy core
- Options: SameBoy, custom LR35902 implementation
- Would require complete system integration rewrite

## Immediate Next Steps

1. **Read tv80_core.v** - Find IR update logic
2. **Trace IR updates** - Understand when/how IR is supposed to update
3. **Check GameBoy Mode** - Verify Mode 3 doesn't break IR updates
4. **Test other opcodes** - See if IR problem affects more than JR
5. **Apply targeted fix** - Ensure IR updates on every M1 cycle

## Test Case for Verification

After fixing IR update, verify with:
```cpp
// Test: Verify IR contains correct opcode
PC=$0150: IR should be $18 (JR)
PC=$0151: IR should be $18 (still in JR execution)
PC=$0152: IR should be $00 (NOP) or $76 (HALT)
```

## Status

🚨 **CRITICAL BUG FOUND** - IR register not updated with fetched opcode  
📊 **Success Rate**: 90.6% (48/53) after MCycles fix  
🎯 **Next Target**: Fix IR update logic to reach ~96% (51/53)  
⏱️ **Blocking**: Cannot proceed with JR fixes until IR update works

## References

- `tv80_core.v` - Core CPU implementation (IR update logic)
- `tv80_mcode.v` - Microcode ROM (IR-based case matching)
- Test results: 53-test comprehensive suite
- Previous analysis: JR_COMPLETE_INVESTIGATION.md (incomplete - missed IR issue)

---

**Recommendation**: Focus on fixing IR update in tv80_core.v. This is the actual root cause. The MCycles fix was correct but insufficient because the microcode never executes if IR matching fails.
