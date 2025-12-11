# IR Register Investigation
## Date: 2025-12-11

## Critical Discovery

The TV80 core's `IR` (Instruction Register) **does NOT contain the instruction opcode** during JR execution!

## Evidence

### Test: test_ir_every_cycle.cpp

Monitored `dbg_cpu_ir` (connected to `gameboy.cpu.i_tv80_core.IR`) during JR instruction:

```
ROM Setup:
$0152 = 0x18  (JR opcode)
$0153 = 0x02  (offset +2)

Actual IR Values Observed:
At PC=$0152 (JR opcode location): IR=$01 (NOT $18!)
At PC=$0153 (offset byte): IR=$01
At PC=$0154 (after): IR=$02
```

**The IR register NEVER contains 0x18!**

## Why This Breaks My Fix

My targeted fix in tv80_core.v line 1358:
```verilog
if (IR == 8'h18)
  PC16_B = { {8{DI_Reg[7]}}, DI_Reg } - 1;
```

This check will **NEVER be true** because IR != 0x18.

## What is IR?

Looking at tv80_core.v:
- Line 63: `input [7:0] dinst;` - instruction data input
- Line 477: `IR <= dinst;` - IR is loaded from dinst during M1 cycle
- In GameBoy wrapper (tv80_gameboy.v line 80): `dinst` is connected to `DI`

## Hypothesis

The TV80/GameBoy core may:
1. Use IR for internal state tracking rather than opcode storage
2. Have a bug where dinst is not properly connected during instruction fetch
3. Operate differently in GameBoy Mode 3 (LR35902 compatibility)

The values IR=$01 and IR=$02 suggest IR might be tracking:
- Instruction prefix/mode
- Execution state
- Something other than the actual opcode

## Alternative Approaches

### Option 1: Use DI_Reg Directly ❌ Won't Work
- DI_Reg contains the OFFSET byte (0x02), not the opcode
- Can't distinguish JR from other 2-byte instructions

### Option 2: Use MCycle Pattern ⚠️ Risky
- Unconditional JR has specific MCycle count (3 cycles)
- But so do other instructions
- False positives likely

### Option 3: Check Previous PC or Fetch Cycle ⭐ Possible
- Track what was fetched at PC-2 (opcode location)
- Compare current PC vs previous PC to detect JR execution

### Option 4: Use Different Register ❓ Unknown
- Check if there's a different register that holds the opcode
- May need to search tv80_core.v more thoroughly

### Option 5: Fix at Microcode Level ⚠️ Complex
- Modify TV80's microcode/state machine for JR
- Requires deep TV80 internals knowledge
- High risk of breaking other instructions

## Recommendation

**Investigate if there's an opcode register** that's separate from IR, or **track instruction fetches** to identify when JR is being executed.

Alternatively, accept that TV80 has fundamental bugs and consider:
1. Switching to a different GameBoy CPU core (more work)
2. Extensive TV80 microcode debugging (very time-consuming)
3. Living with broken JR instructions (game won't work)

## Files Checked

- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/tv80/rtl/core/tv80_core.v`
- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/rtl/tv80_gameboy.v`
- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/gameboy_sim.v`

## Next Steps

1. Search tv80_core.v for other registers that might hold opcode
2. Check if there's an instruction decode signal we can use
3. Consider tracking PC history to identify JR execution
4. May need to revert fix and investigate TV80 microcode more deeply
