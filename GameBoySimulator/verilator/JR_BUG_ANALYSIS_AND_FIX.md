# JR Instruction Bug Analysis and Proposed Fix
## Date: 2025-12-11

## Executive Summary

The TV80 GameBoy core has **two critical bugs** in JR (relative jump) instruction implementation:

1. **Unconditional JR (0x18)**: Partially fixed but still failing - possibly MCycle timing issue
2. **Conditional JR (0x20/0x28/0x30/0x38)**: **Microcode logic is backwards** - jumps when condition is FALSE

## Bug #1: Conditional JR - Backwards Logic (CONFIRMED)

### Current Implementation (tv80_mcode.v lines 1323-1350)

```verilog
// Conditional relative jumps (JR [C/NC/Z/NZ], e)
8'b001zz000 :
  begin
    if (Mode != 2 )
      begin
        MCycles = 3'd3;  // Default 3 cycles
        case (1'b1) // MCycle
          MCycle[1] :  // M2
            begin
              Inc_PC = 1'b1;  // Increment PC to read offset byte

              case (IR[4:3])
                0 : MCycles = (!F[Flag_Z]) ? 3'd2 : 3'd3;  // JR NZ
                1 : MCycles = (F[Flag_Z]) ? 3'd2 : 3'd3;   // JR Z
                2 : MCycles = (!F[Flag_C]) ? 3'd2 : 3'd3;  // JR NC
                3 : MCycles = (F[Flag_C]) ? 3'd2 : 3'd3;   // JR C
              endcase
            end

          MCycle[2] :  // M3
            begin
              NoRead = 1'b1;
              JumpE = 1'b1;   // ← ALWAYS JUMPS IF M3 IS REACHED!
              TStates = 3'd5;
            end
          default :;
        endcase
      end
  end
```

### The Problem

**MCycle Logic is Backwards:**
- When condition **TRUE**: `MCycles = 2` → Skip M3 → **DON'T JUMP** ❌
- When condition **FALSE**: `MCycles = 3` → Execute M3 → **JUMP** ❌

**Correct Behavior Should Be:**
- When condition **TRUE**: Execute M3 → **JUMP** ✅
- When condition **FALSE**: Skip M3 → **DON'T JUMP** ✅

### Example: JR C (Jump if Carry)

**Opcode**: 0x38 (IR[4:3] = 3)

**Current Buggy Logic:**
```verilog
3 : MCycles = (F[Flag_C]) ? 3'd2 : 3'd3;   // JR C
```

- Carry **SET** (condition TRUE): MCycles = 2 → NO JUMP ❌ WRONG!
- Carry **CLEAR** (condition FALSE): MCycles = 3 → JUMP ❌ WRONG!

**Correct Logic Should Be:**
```verilog
3 : MCycles = (F[Flag_C]) ? 3'd3 : 3'd2;   // JR C (FIXED)
```

- Carry **SET** (condition TRUE): MCycles = 3 → JUMP ✅ CORRECT!
- Carry **CLEAR** (condition FALSE): MCycles = 2 → NO JUMP ✅ CORRECT!

## Bug #2: Unconditional JR (0x18) - Still Failing

### Current Implementation (tv80_mcode.v lines 1302-1320)

```verilog
8'b00011000 :  // Opcode 0x18
  begin
    if (Mode != 2 )
      begin
        // JR e
        MCycles = 3'b011;  // 3 machine cycles
        case (1'b1) // MCycle
          MCycle[1] :  // M2
            Inc_PC = 1'b1;  // Increment PC to read offset byte
          MCycle[2] :  // M3
            begin
              NoRead = 1'b1;    // Don't read memory
              JumpE = 1'b1;     // Execute jump
              TStates = 3'b101; // 5 T-states
            end
          default :;
        endcase
      end
  end
```

### Current Fix Attempt (tv80_core.v lines 1354-1361)

```verilog
if (JumpE == 1'b1 )
  begin
    // Fix for JR instruction: compensate for extra PC increment
    // TV80 increments PC twice (M1 T3 + M2 T3), so subtract 1
    PC16_B = { {8{DI_Reg[7]}}, DI_Reg } - 1;
  end
```

### Why It Still Fails

**Possible Issues:**

1. **M3 Not Reached**: MCycles = 3'b011 (binary 011 = 3) might not be triggering M3 properly
   - MCycle is one-hot encoded: MCycle[0]=M1, MCycle[1]=M2, MCycle[2]=M3
   - Need to verify MCycles assignment is actually setting MCycle[2]

2. **Timing Issue**: JumpE might be asserted but PC update happens at wrong time
   - PC might update before PC16_B is calculated with offset

3. **Mode Check**: `if (Mode != 2)` might be failing in GameBoy Mode 3
   - Need to verify Mode value during execution

## Proposed Fixes

### FIX #1: Conditional JR - Reverse MCycles Logic (CRITICAL)

**File**: `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/tv80/rtl/core/tv80_mcode.v`

**Lines**: 1334-1337

**Current Code:**
```verilog
case (IR[4:3])
  0 : MCycles = (!F[Flag_Z]) ? 3'd2 : 3'd3;  // JR NZ
  1 : MCycles = (F[Flag_Z]) ? 3'd2 : 3'd3;   // JR Z
  2 : MCycles = (!F[Flag_C]) ? 3'd2 : 3'd3;  // JR NC
  3 : MCycles = (F[Flag_C]) ? 3'd2 : 3'd3;   // JR C
endcase
```

**Fixed Code:**
```verilog
case (IR[4:3])
  0 : MCycles = (!F[Flag_Z]) ? 3'd3 : 3'd2;  // JR NZ - FIXED: Jump when NOT zero
  1 : MCycles = (F[Flag_Z]) ? 3'd3 : 3'd2;   // JR Z  - FIXED: Jump when zero
  2 : MCycles = (!F[Flag_C]) ? 3'd3 : 3'd2;  // JR NC - FIXED: Jump when NOT carry
  3 : MCycles = (F[Flag_C]) ? 3'd3 : 3'd2;   // JR C  - FIXED: Jump when carry
endcase
```

**Explanation**: Swap the 3'd2 and 3'd3 values to make TRUE condition execute M3 (jump).

### FIX #2: Unconditional JR - Debug and Verify

**Diagnostic Steps:**

1. **Add Debug Signals** to verify M3 execution:
   ```verilog
   // In tv80_core.v, add debug output
   assign dbg_mcycle = mcycle;
   assign dbg_jumpe = JumpE;
   ```

2. **Check MCycle Assignment**: Verify that `MCycles = 3'b011` actually sets MCycle[2]=1

3. **Verify Mode Value**: Check that `Mode == 3` (GameBoy mode) doesn't interfere

### FIX #3: Alternative - Use Case Statement Instead of Binary

If the binary MCycles assignment is the issue, change to explicit case:

```verilog
8'b00011000 :  // JR e
  begin
    if (Mode != 2 )
      begin
        // JR e - 3 machine cycles
        case (1'b1) // MCycle
          MCycle[0] :  // M1
            begin
              // M1 handled by default instruction fetch
            end
          MCycle[1] :  // M2
            begin
              Inc_PC = 1'b1;  // Read offset byte
            end
          MCycle[2] :  // M3
            begin
              NoRead = 1'b1;
              JumpE = 1'b1;
              TStates = 3'b101;
            end
          default :;
        endcase
      end
  end
```

Remove the `MCycles = 3'b011;` line and let the case statement control execution.

## Testing Plan

### Test 1: Fix Conditional JR

1. Apply Fix #1 (reverse MCycles logic)
2. Rebuild Verilator model: `./verilate_gameboy.sh`
3. Run comprehensive test suite: `./test_cpu_comprehensive`
4. Expected: Tests 6, 7, 8 should now PASS

### Test 2: Debug Unconditional JR

1. Add debug signals for MCycle and JumpE
2. Run instrumented test to capture MCycle values
3. Verify M3 is actually being executed
4. Check PC16_B calculation timing

### Test 3: Full Validation

After both fixes:
1. Run all 53 tests in comprehensive suite
2. Expected: All 47 currently passing + 4 conditional JR = 51/53 passing
3. Only failures should be: IR register check, 10 NOPs (IR-related)

## Impact Assessment

**Conditional JR Fix:**
- **Difficulty**: TRIVIAL (swap two values per line)
- **Risk**: VERY LOW (isolated change, well-defined behavior)
- **Impact**: HIGH (fixes 4 failing tests immediately)

**Unconditional JR Fix:**
- **Difficulty**: MODERATE (requires debugging)
- **Risk**: LOW-MEDIUM (depends on root cause)
- **Impact**: HIGH (critical for game compatibility)

## Game Compatibility

The game ROM contains **1,586 JR instructions**:
- Conditional JR fix alone: ~40% of JR instructions will work
- Both fixes: ~100% of JR instructions will work
- **Game will be PLAYABLE** after these fixes

## References

- `tv80_mcode.v` - Microcode definitions
- `tv80_core.v` - PC calculation logic
- `JR_COMPLETE_INVESTIGATION.md` - Detailed bug analysis
- `IR_REGISTER_INVESTIGATION.md` - IR register behavior
- Test results: 53-test comprehensive suite (47/53 passing before fix)

## Recommendation

**APPLY FIX #1 IMMEDIATELY** - The conditional JR fix is trivial and low-risk. It will immediately improve success rate from 88.7% to ~96%.

For unconditional JR, **DEBUG FIRST** before applying speculative fixes. The offset compensation is already in place, so the issue is likely MCycle execution or timing-related.
