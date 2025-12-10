# CPU BUG FOUND - Reset Vector Failure

## Test Results Summary

Comprehensive CPU test reveals **CRITICAL BUG**: CPU does not start at $0000 after reset!

### Test 1: Basic Instructions
```
CPU Trace:
  [   0] PC=$0006 rd=0 wr=1  ← FIRST ADDRESS!
  [  29] PC=$0007 rd=1 wr=1
  [  93] PC=$0008 rd=1 wr=1
  [ 157] PC=$0009 rd=1 wr=1
  [ 221] PC=$0007 rd=1 wr=1  ← Looping $0007-$0009
```

**Expected:** PC should start at $0000  
**Actual:** PC starts at $0006  
**Result:** ❌ FAIL - CPU never reaches $0000, $0003, or $0005

### Test 2: Real Boot ROM Execution
```
CPU Trace:
  [   0] PC=$0008 rd=0 wr=1  ← FIRST ADDRESS!
  [  41] PC=$0009 rd=1 wr=1
  [ 105] PC=$000A rd=1 wr=1
  [ 169] PC=$000B rd=1 wr=1
  [ 233] PC=$0006 rd=1 wr=1
  [ 297] PC=$8005 rd=1 wr=1  ← VRAM write (tile copy loop)
  [ 361] PC=$0007 rd=1 wr=1
```

**Pattern:** CPU executing logo tile copy loop ($0006-$000B) but **never hits initialization code**

**Missing execution:**
- $0000: LD SP, $FFFE    ← NEVER EXECUTED
- $0003: CALL $00D5      ← NEVER EXECUTED  
- $0005: (subroutine)    ← NEVER EXECUTED

## Root Cause Analysis

### The Bug

**The GameBoy CPU (GBse core) does not properly initialize PC to $0000 on reset.**

Instead, PC appears to be:
1. Uninitialized (random value)
2. Or initialized to wrong address
3. Or jumping mid-execution due to reset timing issue

### Why This Causes Reset Loop in GUI

1. Real DMG boot ROM starts:
   ```
   $0000: 31 FE FF    LD SP, $FFFE    ← Sets stack pointer
   $0003: CD D5 05    CALL $00D5      ← Calls delay subroutine
   $0005: 26 FE       LD H, $FE       ← Logo copy setup
   ```

2. CPU skips $0000-$0005, jumps directly to $0006-$000B (tile copy loop)

3. Tile copy loop runs WITHOUT stack pointer being set (SP = random!)

4. Loop tries to decrement counter or call subroutine

5. Stack operations fail → CPU crashes or resets

6. Reset brings CPU back to... $0006 again (not $0000!)

7. Infinite loop of partial executions and crashes

### Why Simple Test Programs Work

Test programs that start at $0006-$0009 accidentally work because CPU happens to land there!

Programs expecting $0000 start fail completely.

## GBse CPU Core Investigation Needed

The GBse CPU core is likely:

1. **Missing reset logic for PC:**
   ```verilog
   always @(posedge CLK_n) begin
       if (RESET_n == 0) begin
           PC <= 16'h0000;  // ← Is this missing?
       end
   end
   ```

2. **Reset timing issue:** Reset may be too short or CPU needs more cycles

3. **Boot ROM interaction:** Boot ROM enable might interfere with reset vector

## Next Steps

1. **Examine GBse CPU core reset logic** in gameboy_core/rtl/cpu/ directory
2. **Check PC initialization** in CPU state machine
3. **Verify reset signal timing** - may need longer hold time
4. **Test with extended reset cycles** in simulator

## Files to Investigate

- `gameboy_core/rtl/cpu/GBse*.v` - Main CPU core
- `gameboy_core/rtl/gb.v` - CPU instantiation and reset logic
- Reset signal path from top to CPU core

## Verification

Once fixed, CPU trace should show:
```
  [   0] PC=$0000 rd=0 wr=1  ← Starts at reset vector!
  [  XX] PC=$0001 rd=1 wr=1
  [  XX] PC=$0002 rd=1 wr=1  
  [  XX] PC=$0003 rd=1 wr=1
  [  XX] PC=$0005 rd=1 wr=1  ← Logo scroll subroutine
```

This will allow boot ROM to execute properly and fix the GUI reset loop issue!
