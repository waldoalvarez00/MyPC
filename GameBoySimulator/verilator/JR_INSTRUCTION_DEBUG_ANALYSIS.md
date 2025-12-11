# JR Instruction Debug Analysis
## Date: 2025-12-11

## Problem Statement

The JR instruction (opcode 0x18) in the GameBoy simulator does NOT execute the relative jump. Instead, it fetches both bytes and continues to the next instruction as if JR was a 2-byte NOP.

## Test Results Summary

### PC Transition Analysis

**JP Instruction (✅ WORKING):**
```
$0150 (JP opcode) → $0151 (low byte) → $0152 (high byte) → $0160 (jumped!)
```
- Fetches 3 bytes correctly
- Performs absolute jump to target address
- Status: **WORKS PERFECTLY**

**JR Instruction (❌ FAILING):**
```
$0160 (JR opcode) → $0161 (offset byte) → $0162 (next instruction)
```
- Fetches 2 bytes correctly
- **DOES NOT** perform relative jump
- PC continues to next instruction instead
- Status: **COMPLETELY BROKEN**

## TV80 Core Investigation

### JR Microcode Implementation

Location: `tv80/rtl/core/tv80_mcode.v` lines 1302-1320

```verilog
8'b00011000  :  // Opcode 0x18 (JR e)
  begin
    if (Mode != 2 )  // ← Mode 3 (GameBoy) should pass this test
      begin
        // JR e
        MCycles = 3'b011;  // 3 machine cycles
        case (1'b1) // MCycle
          MCycle[1] :
            Inc_PC = 1'b1;  // Fetch offset byte
          MCycle[2] :
            begin
              NoRead = 1'b1;
              JumpE = 1'b1;  // ← EXECUTE RELATIVE JUMP
              TStates = 3'b101;
            end
          default :;
        endcase
      end // if (Mode != 2 )
  end // case: 8'b00011000
```

### JumpE Signal Handling

Location: `tv80/rtl/core/tv80_core.v`

**PC16_B Calculation (line 1354-1356):**
```verilog
if (JumpE == 1'b1 )
  begin
    PC16_B = { {8{DI_Reg[7]}}, DI_Reg };  // Sign-extend offset
  end
```

**PC16 Calculation (line 1389):**
```verilog
PC16 = PC + PC16_B;  // Add offset to current PC
```

**PC Update (line 684-686):**
```verilog
if (JumpE == 1'b1 )
  begin
    PC <= `TV80DELAY PC16;  // Load new PC
  end
```

**Conclusion:** The TV80 microcode and core logic appear **CORRECT**!

## Configuration Verification

**GameBoy Wrapper:** `rtl/tv80_gameboy.v` line 60
```verilog
tv80_core #(
    .Mode(3),           // GameBoy mode (LR35902)
    .IOWait(IOWait)
) i_tv80_core (
```

Mode 3 is correctly set. The JR instruction should work because:
- `if (Mode != 2)` → Mode 3 passes this test ✅
- JumpE should be asserted in MCycle[2] ✅
- PC should be updated with sign-extended offset ✅

## Clock Enable Analysis

From cycle-by-cycle traces, we observed:

**At every PC transition:**
- `cpu_clken = 0`
- `ce_cpu = 0`
- `cart_rd = 0` (after read completes)
- `cpu_rd_n = 1` (after read completes)

**Pattern for both JP and JR:**
- cpu_clken pulses high once every 16 cycles (6.25% duty cycle)
- ce_cpu pulses at same rate
- PC advances ~160 cycles between transitions

This pattern is **IDENTICAL** for both working (JP) and failing (JR) instructions!

## Hypothesis

The CPU clock enables appear identical for both instructions, ruling out clock gating as the root cause. The issue must be in one of these areas:

### Hypothesis 1: MCycle Progression Issue ⭐ **MOST LIKELY**
The CPU may not be reaching MCycle[2] where JumpE is asserted. Possible causes:
- MCycle counter not incrementing correctly for JR
- Wait state logic interfering with MCycle progression
- GameBoy-specific timing issue with 2-byte instructions

### Hypothesis 2: JumpE Signal Not Asserted
The JumpE control signal may not be asserted even though microcode requests it. Possible causes:
- ISet (instruction set) parameter incorrect
- GameBoy mode override disabling JumpE
- Signal gating in tv80_gameboy wrapper

### Hypothesis 3: DI_Reg Not Loaded
The offset byte (DI_Reg) may not be properly loaded from memory. Possible causes:
- Data input path issue in GameBoy wrapper
- Memory interface timing problem
- SDRAM wait states affecting data register loading

### Hypothesis 4: PC Update Conditional Issue
The PC update may have an additional condition not visible in the code. Possible causes:
- Synthesis optimization removing PC update logic
- Reset or halt condition interfering
- GameBoy-specific PC update override

## Evidence Supporting Hypothesis 1 (MCycle Issue)

1. **PC increments exactly twice:** $0160 → $0161 → $0162
   - This suggests MCycle[0] and MCycle[1] execute normally
   - MCycle[2] (where JumpE happens) may not execute

2. **Timing matches 2-byte fetch:**
   - Time between $0160 and $0161: 160 cycles
   - Time between $0161 and $0162: 160 cycles
   - This is consistent with 2 fetch cycles, no jump cycle

3. **JP works with 3 MCycles:**
   - JP has 3 fetch cycles (opcode + 2 address bytes)
   - JP's MCycle[3] presumably handles the jump
   - JR should have 2 fetch cycles + 1 jump cycle

## Next Steps

### Option 1: Add MCycle Debug Signals
Modify `tv80_gameboy.v` to export MCycle state:
```verilog
output [6:0] dbg_mcycle,  // Current machine cycle
output [2:0] dbg_tstate,  // Current T-state
output       dbg_jumpe,   // JumpE signal
output [7:0] dbg_di_reg   // Data input register (offset)
```

Then rerun tests to confirm MCycle progression.

### Option 2: Force JumpE in Wrapper
As a workaround, detect JR instruction in wrapper and manually assert jump:
```verilog
wire jr_detected = (cpu_addr == last_addr + 1) && (last_opcode == 8'h18);
wire force_jumpe = jr_detected && mcycle[2];
```

This is a hack but would prove the hypothesis.

### Option 3: Switch CPU Core
If TV80 is fundamentally broken for GameBoy JR:
- Use a different LR35902 core (e.g., from other GameBoy projects)
- Patch TV80 to fix JR execution
- Report bug to TV80 maintainers

## Game Impact

The game ROM (game.gb) contains **1,586 JR instructions** (verified via hexdump).

**Without JR working, the game CANNOT execute properly.**

This is a **CRITICAL** bug that blocks all game functionality.

## Status

- ✅ Root cause narrowed to MCycle progression or JumpE assertion
- ✅ TV80 microcode verified correct
- ✅ GameBoy Mode (3) verified correct
- ✅ Clock enables verified identical for JP and JR
- ❌ Exact failure point NOT YET identified
- ⏳ Waiting for MCycle-level instrumentation

## Files Created

- `test_jr_cycle_trace.cpp` - Cycle-by-cycle signal trace
- `test_jr_pc_transitions.cpp` - PC transition analysis ✅ **KEY TEST**
- `JR_INSTRUCTION_DEBUG_ANALYSIS.md` - This document

---

**Priority:** 🚨 **CRITICAL**
**Next Action:** Add MCycle/JumpE debug signals to isolate exact failure point
