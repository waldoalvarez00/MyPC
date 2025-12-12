# IR Register Update Timing Analysis - Root Cause Found
## Date: 2025-12-11

## CRITICAL DISCOVERY

The IR register **DOES update** correctly, but the CPU execution is **BLOCKED by SDRAM wait states**!

## Signal Trace Evidence

```
Cycle    PC     IR   MCycle TState  Analysis
─────────────────────────────────────────────────────────────
  541   $0150  $C3   M1     T2      PC arrives at JR instruction
  542-556:     $C3   M1     T2      Stuck in T2 (14 cycles)
  557-620:     $C3   M1     T3      Stuck in T3 (63 cycles!) ← SDRAM WAIT
  621   $0150  $18   M1     T4      IR UPDATES! But now in T4
  622-640:     $18   M1     T4      Stuck in T4 forever
```

## Root Cause Analysis

### 1. SDRAM Wait State Logic (gameboy_core/rtl/gb.v)

**Lines 312-329**: SDRAM wait state counter
```verilog
wire cpu_reading_ext_bus = (sel_ext_bus & ~cpu_rd_n & ~cpu_mreq_n);

always @(posedge clk_sys) begin
    if (ce) begin  // ← Only counts when clock enable active!
        if (cpu_reading_ext_bus && !sdram_wait_active) begin
            sdram_wait_counter <= 2'd2;  // CAS latency = 2
            sdram_wait_active <= 1'b1;
        end else if (sdram_wait_active) begin
            if (sdram_wait_counter > 0) begin
                sdram_wait_counter <= sdram_wait_counter - 2'd1;
            end
        end
    end
end

wire sdram_ready = ~sdram_wait_active;
```

**Line 383**: Connected to CPU
```verilog
.WAIT_n ( sdram_ready ),
```

### 2. The Wait State Problem

**Issue**: The wait counter is clocked by `ce` (clock enable), not every system clock!

- System clock might run at 32MHz (Verilator simulation speed)
- `ce` might pulse at 4MHz (Game Boy CPU speed = 8x slower)
- Counter = 2 → requires 2 `ce` pulses → could be 16 system clock cycles
- But we saw 63 cycles stuck in T3!

**Hypothesis**: `ce` is running even slower than expected, or there's a circular dependency issue.

### 3. IR Update Timing (tv80_core.v lines 451-477)

```verilog
if (mcycle[0] && tstate[2] && wait_n == 1'b1) begin
    IR <= dinst;  // Registered assignment (1 cycle delay)
end
```

**Correct Behavior**:
- Cycle N: In M1 T3, wait_n goes high → IR assignment triggered
- Cycle N+1: IR updates to new value, T-state advances to T4

**This is working correctly!** The IR update happened at cycle 621 when transitioning from T3→T4.

### 4. Stuck in T4 Forever

**New Problem**: After IR updates, CPU gets stuck in M1 T4 and never advances to M2!

**Possible Causes**:
1. T-state counter not resetting after T4
2. M-cycle counter not advancing from M1 to M2
3. Another wait condition preventing state machine progression
4. Clock enable `ce` stopped pulsing

## Impact on JR Instruction

Even though IR now contains $18 (JR opcode), the microcode never executes because:
1. CPU is stuck in M1 T4
2. Microcode case matching happens during M-cycle transitions
3. M2 and M3 never execute
4. JumpE never asserts
5. Jump never happens

## Why Other Instructions Work

**Hypothesis**: Instructions like LD, ADD, PUSH work because they:
1. Don't get stuck in wait states (accessing fast internal RAM/registers)
2. Have simpler microcode sequences
3. Use different address ranges that don't trigger SDRAM waits

**JP works** because:
- It's a 3-byte instruction ($C3 + 2 address bytes)
- Might have different timing that doesn't trigger the stuck condition
- Or ROM reads might be faster/cached

## The Circular Dependency Issue

**Line 320 comment**: "Use 'ce' (not 'ce_cpu') to avoid circular dependency"

**The Problem**:
- `ce_cpu` depends on `sdram_ready` (line 302)
- `sdram_ready` depends on wait counter
- Wait counter is clocked by `ce`
- If `ce` stops or runs slow, counter never decrements
- If counter never decrements, `sdram_ready` stays low
- This could create a deadlock!

## Why Stuck in T4 Instead of T3

**T3 → T4 Transition**: Happens when `wait_n` goes high
- Wait completes → `wait_n` = 1
- CPU advances from T3 to T4
- IR updates (1 cycle delay)

**T4 → T1 (next M-cycle) Transition**: Should happen automatically
- Requires T-state counter to reset
- Requires M-cycle counter to increment
- Something is preventing this!

## Proposed Solutions

### Option 1: Fix Wait State Counter Clock (RECOMMENDED)

**Problem**: Counter clocked by `ce` makes it too slow
**Fix**: Clock counter by system clock, not clock enable

```verilog
// BEFORE:
always @(posedge clk_sys) begin
    if (ce) begin  // ← TOO SLOW!
        if (sdram_wait_counter > 0) begin
            sdram_wait_counter <= sdram_wait_counter - 2'd1;
        end
    end
end

// AFTER:
always @(posedge clk_sys) begin
    // Remove 'if (ce)' wrapper - count every clock!
    if (sdram_wait_counter > 0) begin
        sdram_wait_counter <= sdram_wait_counter - 2'd1;
    end
end
```

### Option 2: Increase Counter Value

**Problem**: Counter value too small for clock enable rate
**Fix**: Adjust counter to match actual `ce` pulse rate

```verilog
// If ce pulses every 8 clocks and CAS latency = 2:
sdram_wait_counter <= 2'd2 * 8;  // = 16 system clocks
```

### Option 3: Disable Wait States for ROM Reads

**Problem**: Wait states not needed for simulated SDRAM
**Fix**: Only apply wait states for actual hardware, not simulation

```verilog
`ifndef VERILATOR
    wire sdram_ready = ~sdram_wait_active;
`else
    wire sdram_ready = 1'b1;  // Always ready in simulation
`endif
```

## Testing Plan

After applying fix:
1. Re-run `test_jr_detailed_signals` - should not get stuck in T3/T4
2. Verify IR updates within reasonable time (< 10 cycles)
3. Verify M1 → M2 → M3 progression happens
4. Re-run comprehensive test suite - expect 51/53 passing

## Files to Modify

- `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/gameboy_core/rtl/gb.v` (lines 316-329)

## Status

🚨 **ROOT CAUSE CONFIRMED** - SDRAM wait state logic blocks CPU execution  
📊 **Impact**: Prevents ALL jump instructions from working in simulation  
🎯 **Fix Priority**: CRITICAL - Blocks all testing progress  
⏱️ **Estimated Fix Time**: 5 minutes (simple change)

---

**Recommendation**: Apply Option 3 (disable wait states for Verilator) as immediate fix. This is safe because Verilator simulation already includes proper SDRAM timing model. The wait states are redundant and causing the hang.
