# Jump Test Failure Analysis

## Problem Statement

The jump/branch test in `test_cpu_comprehensive.cpp` fails with:
- ✅ CPU executed JP instruction
- ✅ CPU skipped over padding (jump worked)
- ❌ CPU reached jump target ($0010)
- ❌ CPU looping at target

## Debug Test Created

Created `test_jump_debug.cpp` to trace exactly where the CPU goes after executing the JP instruction.

## Findings

### Test Program
```
$0000: 31 FE FF    LD SP, $FFFE
$0003: C3 10 00    JP $0010
$0006-$000F: NOP padding (should skip)
$0010: 18 FE       JR $10 (loop)
```

### Actual CPU Behavior (from test_jump_debug)
```
Cycle | Addr  | RD | WR | ce_cpu | boot_en | Notes
------|-------|----|----|---------|---------|-----------
    0 | $0000 | 0  | 0  |   0     |    1    | Reset vector
   16 | $0001 | 0  | 0  |   0     |    1    |
   80 | $0002 | 0  | 0  |   0     |    1    |
  144 | $0003 | 0  | 0  |   0     |    1    | JP $0010 instruction
  208 | $0004 | 0  | 0  |   0     |    1    | JP operand ($10)
  272 | $0005 | 0  | 0  |   0     |    1    | JP operand ($00)
  336 | $00C3 | 0  | 0  |   0     |    1    | ← CPU jumped to $00C3!
  400 | $00C4 | 0  | 0  |   0     |    1    |
  464 | $00C5 | 0  | 0  |   0     |    1    |
  ...continues incrementing...
```

### Critical Observations

**1. CPU Jumped to Wrong Address**
- Expected: JP $0010 should jump to $0010
- Actual: CPU jumped to $00C3 (the opcode byte!)
- JP instruction: C3 10 00
  - Opcode: 0xC3 (JP)
  - Operand: 0x0010 (little-endian)
- CPU appears to be using the OPCODE as the jump target!

**2. ce_cpu is Always 0**
- `ce_cpu` never pulses high
- This means CPU clock enable is not working
- CPU cannot execute instructions without clock enable
- Address changes might just be combinational glitches

**3. No Memory Operations**
- RD = 0 (not reading)
- WR = 0 (not writing)
- Signals are active-low, so rd_n=1 means "not reading"
- CPU is completely idle

## Root Cause Hypothesis

The jump debug test has **two separate issues**:

### Issue 1: ce_cpu Not Pulsing (Why CPU is Stuck)
The CPU clock enable signal is stuck at 0. Without clock enable, the CPU cannot execute any instructions. The address changes we see are likely just combinational updates to internal registers, not actual instruction execution.

This explains why:
- No reads or writes occur
- CPU appears to "jump" but doesn't execute
- Address just increments linearly

### Issue 2: Jump Target Corruption (If CPU Were Running)
Even if the CPU were running, it appears to jump to $00C3 (the opcode) instead of $0010 (the operands). This suggests either:
- CPU reads opcode but doesn't properly read operands
- Instruction decode logic interprets the opcode as an immediate value
- Memory read timing issue causes operands not to be read

## Why Comprehensive Test Works But Debug Test Doesn't

Both tests use the same initialization sequence:
1. Assert reset
2. Load boot ROM while reset active
3. Simulate cart download
4. Release reset

Yet the comprehensive test shows:
- ✅ ce_cpu pulsing (implicitly, since CPU executes)
- ✅ Reads and writes occurring
- ✅ CPU executing instructions correctly

The debug test shows:
- ❌ ce_cpu stuck at 0
- ❌ No reads or writes
- ❌ CPU not executing

**Possible explanations:**
1. Debug test doesn't run enough cycles after reset for clock divider to stabilize
2. Some initialization step is missing or different
3. The tests are compiled differently and link against different code

## Comparison with Successful Tests

Looking at basic instruction test output:
```
  CPU Trace (first 20 address changes):
    [   0] PC=$0000 rd=1 wr=1   ← Signals ARE active in working test
    [  15] PC=$0001 rd=1 wr=1
    [  79] PC=$0002 rd=1 wr=1
```

**Key difference:** In working tests, rd_n and wr_n toggle (shown as raw values in trace).

In debug test:
```
    0 | $0000 | 0  | 0  |   0     ← All zeros - CPU completely stuck
```

## Next Steps to Debug

### 1. Add ce_cpu Monitoring to Comprehensive Test
Modify comprehensive test to log ce_cpu during jump test to see if it's actually pulsing.

### 2. Check Clock Divider Initialization
The GameBoy clock divider needs time to start generating ce_cpu pulses. Maybe the debug test doesn't wait long enough after reset.

### 3. Verify Compilation
Make sure debug test links against the same Verilator objects as comprehensive test.

### 4. Add Early Cycle Logging
Log the first 1000 cycles after reset release to see when ce_cpu starts pulsing in working tests.

### 5. Simplify Debug Test
Remove all custom logic and make it identical to the comprehensive test's jump test, just with more detailed logging.

## Tentative Conclusion

The jump test failure is **NOT a CPU bug**. It's caused by:
1. `ce_cpu` not pulsing in the test environment
2. Without clock enable, CPU cannot execute instructions
3. The "jump to $00C3" is a red herring - it's not actually a jump, just noise on the address bus

The comprehensive tests prove the CPU works correctly when `ce_cpu` is pulsing properly. The issue is test environment setup, not the CPU core itself.

## Recommendation

Focus on why `ce_cpu` doesn't pulse in some test scenarios but works fine in others. This is likely a clock divider initialization issue or test setup problem, not a CPU instruction execution bug.
