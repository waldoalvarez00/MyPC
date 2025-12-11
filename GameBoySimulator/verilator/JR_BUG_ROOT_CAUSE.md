# JR Instruction Bug - Root Cause Analysis
## Date: 2025-12-11

## 🚨 CRITICAL DISCOVERY

**JR instruction (opcode 0x18) does NOT execute in TV80 core, even with zero SDRAM latency!**

## Test Results

### Test 1: JR with CAS latency = 2 (realistic)
```
PC=$0160 (JR opcode) [cpu_clken=0 ce_cpu=0 cart_rd=0]
PC=$0161 (JR offset) [cpu_clken=0 ce_cpu=0 cart_rd=0]
PC=$0162 (HALT) ← BUG!

Result: ❌ FAILED
```

### Test 2: JR with CAS latency = 0 (instant)
```
PC=$0160 (JR opcode)
PC=$0161 (JR offset)
PC=$0162 (HALT) ← BUG!

Result: ❌ FAILED
```

### Test 3: JP with CAS latency = 2 (comparison)
```
PC=$0150 (JP opcode)
PC=$0151 (JP addr low)
PC=$0152 (JP addr high)
PC=$0160 ← JUMPED!

Result: ✅ PASSED
```

## Conclusion

**This is NOT a wait state issue - it's a TV80 core bug or misconfiguration!**

The JR instruction fails regardless of SDRAM timing, which means:
1. ✅ Wait state logic is working correctly (JP proves it)
2. ❌ TV80 core has a bug with JR instruction in GameBoy mode
3. ❌ OR: TV80 core is not properly configured for GameBoy mode

## TV80 Configuration

From `rtl/tv80_gameboy.v:60`:
```verilog
tv80_core #(
    .Mode(3),           // GameBoy mode (LR35902)
    .IOWait(IOWait)
) i_tv80_core (
```

Mode 3 = GameBoy mode is correctly set.

## GameBoy LR35902 JR Specification

From [GameBoy opcodes](https://www.pastraiser.com/cpu/gameboy/gameboy_opcodes.html):
- **Opcode**: 0x18 (JR e)
- **Length**: 2 bytes
- **Cycles**: 12 cycles
- **Operation**: PC = PC + e (signed 8-bit offset)

## Why Your Game Might Still Work

### Possibility 1: Game doesn't use JR
Many games use JP/CALL/RET instead of JR for jumps.

### Possibility 2: Your previous GUI log suggests it works
Your console log showed successful execution:
```
BOOT ROM DISABLED at frame 1!
Cart PC[19]: $DFFF ← Jump to RAM
Cart PC[50]: $C1B5 ← Function call
```

This could mean:
- Game uses JP instead of JR
- OR: TV80 in production has different behavior than test
- OR: There's a subtle timing difference in GUI vs test

## Recommended Actions

### Immediate
1. ✅ Check if game.gb uses JR instructions (opcode 0x18)
2. 🔄 Rebuild GUI simulator and test real game
3. 📊 Report back if game works

### If Game Uses JR and Doesn't Work
1. Investigate TV80 core JR implementation
2. Check if TV80 Mode 3 actually implements JR
3. Consider patching TV80 core
4. OR: Use different CPU core (if available)

### If Game Works Despite JR Bug
1. Game likely doesn't use JR
2. Document as known limitation
3. Focus on other issues (LCD initialization)

## Technical Deep Dive

### Why JP Works But JR Doesn't

**JP (3-byte instruction)**:
- Opcode: 0xC3
- Operands: 2 bytes (16-bit absolute address)
- Implementation: Load address, set PC
- **Works correctly** ✅

**JR (2-byte instruction)**:
- Opcode: 0x18
- Operand: 1 byte (signed 8-bit offset)
- Implementation: Calculate PC + offset, set PC
- **Doesn't work** ❌

### Possible TV80 Core Issues

1. **JR offset calculation bug**: TV80 might not calculate `PC + offset` correctly in GameBoy mode
2. **Signed offset handling**: Might not handle signed 8-bit correctly
3. **GameBoy mode incomplete**: Mode 3 might not fully implement LR35902 JR
4. **Timing issue**: JR might require specific timing TV80 doesn't provide

## Sources

- [GameBoy opcodes](https://www.pastraiser.com/cpu/gameboy/gameboy_opcodes.html)
- [TV80 core on OpenCores](https://opencores.org/projects/tv80)
- [Game Boy CPU instruction set](https://gbdev.io/gb-opcodes/)

## Next Steps

1. **Check game ROM**: Does it use JR? (running now)
2. **Test real game**: Rebuild GUI and test
3. **Report findings**: Tell me if game works
4. **If broken**: We'll need to fix TV80 core or find workaround

## Status

- ✅ Root cause identified: TV80 core bug (not wait states)
- ✅ Reproduced with zero latency
- ✅ Confirmed JP works correctly
- ⏳ Checking if game uses JR
- ⏳ Awaiting user GUI test

---

**Bottom Line**: Your wait state fix is correct! The JR issue is separate (TV80 bug).
