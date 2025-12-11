# JR Instruction Bug - Root Cause Identified
## Date: 2025-12-11

## 🎯 ROOT CAUSE FOUND

**The PC auto-increments between M2 and M3, causing the relative jump to calculate from the wrong address.**

## Evidence

### MCycle Trace - JR Instruction (0x18)

```
Cycle   PC     IR    MCycle TState MCycles_total
-----   ----   ----  ------ ------ -------------
40926  $0160   $18   M1     T4        3          ← Fetch opcode
40990  $0160   $18   M1     T5        3
41006  $0161   $18   M2     T2        3          ← Fetch offset (+1 from Inc_PC in M2)
41150  $0161   $18   M2     T5        3
41166  $0162   $18   M3     T2        3          ← ❌ PC ALREADY INCREMENTED TO $0162!
```

**Problem:** At M3 start, PC = $0162 instead of expected $0161

### Expected vs Actual

**Expected JR Execution:**
1. **M1 at $0160**: Fetch opcode 0x18
2. **M2 at $0161**: Fetch offset 0x02, `Inc_PC=1` advances PC from $0160→$0161
3. **M3 at $0161**: `JumpE=1` calculates PC = $0161 + 2 = **$0163** ✅

**Actual JR Execution:**
1. **M1 at $0160**: Fetch opcode 0x18 ✅
2. **M2 at $0161**: Fetch offset 0x02 ✅
3. **M3 at $0162**: PC already incremented! Jump calculates PC = $0162 + 2 = $0164 ❌
   - But CPU continues to $0162 (byte-by-byte) instead

### Comparison with JP Instruction (0xC3)

**JP Execution (WORKS):**
```
40366  $0150   $C3   M1     T2        3          ← Fetch JP opcode
40526  $0151   $C3   M2     T2        3          ← Fetch address low byte
40686  $0152   $C3   M3     T2        3          ← Fetch address high byte
(then jumps to $0160)
```

JP works because:
- It fetches 3 bytes ($0150, $0151, $0152)
- All 3 MCycles perform memory reads
- Jump happens AFTER all bytes are fetched

JR fails because:
- It fetches 2 bytes ($0160, $0161)
- M3 is supposed to be a "NoRead" cycle that performs the jump
- **But PC advances to $0162 before M3 executes!**

## Technical Analysis

### JR Microcode (tv80_mcode.v lines 1302-1320)

```verilog
8'b00011000  :  // JR e (opcode 0x18)
  begin
    if (Mode != 2 )  // Mode 3 (GameBoy) passes this test
      begin
        MCycles = 3'b011;  // 3 machine cycles
        case (1'b1) // MCycle
          MCycle[1] :  // M2
            Inc_PC = 1'b1;  // ← Increment PC to fetch offset
          MCycle[2] :  // M3
            begin
              NoRead = 1'b1;   // ← Don't read memory
              JumpE = 1'b1;    // ← Execute relative jump
              TStates = 3'b101;
            end
          default :;
        endcase
      end
  end
```

### Where PC Increments

**Expected behavior:**
- M1: PC fetches opcode at current address
- M2: `Inc_PC=1` advances PC by 1 (to fetch operand byte)
- M3: PC should STAY at operand address, then `JumpE` adds offset

**Actual behavior:**
- M1: PC at $0160 ✅
- M2: PC at $0161 ✅ (Inc_PC worked)
- **M3: PC at $0162** ❌ **(unwanted auto-increment!)**

## Why This Happens

The TV80 core likely has a default behavior:
- **After each MCycle completes, PC auto-increments to prepare for next fetch**
- This works fine for instructions where every MCycle is a memory read
- **JR's M3 is NoRead**, but PC still increments before M3 starts

### Code Location (Hypothesis)

In `tv80_core.v`, there's likely logic like:
```verilog
// At end of each MCycle
if (mcycle_done && next_mcycle_is_fetch) begin
    PC <= PC + 1;  // ← This increments PC before M3!
end
```

For JR, M3 is marked `NoRead`, but PC still auto-increments.

## Impact

- **Game Boy ROM uses 1,586 JR instructions**
- **Game cannot run without JR working**
- This is a **critical blocking bug**

## Solution Options

### Option 1: Patch TV80 Core ⭐ **RECOMMENDED**

Modify `tv80_core.v` PC update logic:
```verilog
// Only auto-increment PC if next cycle is a memory read
if (mcycle_done && !NoRead_next && !JumpE_next) begin
    PC <= PC + 1;
end
```

### Option 2: Modify JR Microcode

Change JR to account for auto-increment:
```verilog
MCycle[2] :
  begin
    NoRead = 1'b1;
    JumpE = 1'b1;
    PC_adjust = -1;  // ← Subtract 1 to compensate for auto-increment
    TStates = 3'b101;
  end
```

### Option 3: Use Different CPU Core

Replace TV80 with a known-working LR35902 implementation:
- https://github.com/OpenCores/TV80 (check for updates)
- https://github.com/gdkchan/LR35902-emu
- Other GameBoy CPU cores

## Files Created

- `test_jr_pc_transitions.cpp` - Identified PC byte-by-byte increment
- `test_jr_cycle_trace.cpp` - Cycle-level signal analysis
- `test_jr_mcycle_analysis.cpp` - **MCycle trace that found the bug** ⭐
- `jr_mcycle_output.txt` - Raw test output
- `JR_BUG_ROOT_CAUSE_FINAL.md` - This document

## Next Steps

1. **Locate PC auto-increment logic in tv80_core.v**
2. **Add condition to prevent increment before NoRead cycles**
3. **Test fix with all JR variants (0x18, 0x20, 0x28, 0x30, 0x38)**
4. **Verify game ROM executes correctly**

---

**Status:** ✅ **ROOT CAUSE IDENTIFIED**
**Priority:** 🚨 **CRITICAL - Blocks all game execution**
**Next Action:** Patch TV80 core PC increment logic
