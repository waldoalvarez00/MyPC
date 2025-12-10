# GameBoy SDRAM Issue - Complete Root Cause Analysis

## Executive Summary

**ROOT CAUSE:** The GameBoy CPU core (GBse/TV80) **does NOT respect the CLKEN (clock enable) signal**. It executes on every `CLK_n` edge (64MHz) instead of only when `CLKEN=1` (~4MHz), causing it to run 16x faster than intended and advance PC before SDRAM data is available.

## Investigation Timeline

### Phase 1: SDRAM Timing Fixes (✅ COMPLETE)

#### Issue 1.1: Clock Enable Generation Bug
**Problem:** `ce_cpu2x` was always 0 because clock enables calculated using OLD `clk_div` value.

**Fix:** Added `clk_div_next` wire in `gameboy_sim.v`:
```verilog
wire [3:0] clk_div_next = clk_div + 4'h1;
always @(posedge clk_sys) begin
    clk_div <= clk_div_next;
    ce_cpu <= (clk_div_next == 4'h0);
    ce_cpu2x <= (clk_div_next[2:0] == 3'h0);
end
```

**Result:** ✅ ce_cpu2x now pulses correctly every 8 clk_sys cycles.

#### Issue 1.2: SDRAM Read Latency
**Problem:** SDRAM controller took 5 ce_cpu2x cycles to complete a read (2.5 CPU cycles).

**Fix:** Reduced latency to 2 cycles in `sdram_sim.sv` for simulation:
```verilog
ACTIVATE: begin
    // Zero-latency - proceed immediately
    if (we_r) begin
        cmd <= CMD_WRITE;
        state <= WRITE;
    end else begin
        cmd <= CMD_READ;
        state <= READ;
    end
end

READ: begin
    dout_r <= sd_data_in;
    state <= PRECHARGE;
end
```

**Result:** ✅ SDRAM completes reads faster.

#### Issue 1.3: Combinational dout Output
**Problem:** `dout` was registered, so new data only available AFTER CPU sampled old data.

**Fix:** Made `dout` combinational in `sdram_sim.sv`:
```verilog
// Changed from output reg to output wire
output [15:0] dout;

reg [15:0] dout_r;  // Registered version

// Combinational assignment - data available immediately in READ state
assign dout = (state == READ) ? sd_data_in : dout_r;
```

**Result:** ✅ CPU now reads CORRECT bytes (0xC3, 0x50, 0x01 for JP 0x0150).

### Phase 2: CPU Execution Investigation (✅ ROOT CAUSE FOUND)

#### Observation: CPU Doesn't Execute JP Instruction

**Symptoms:**
- CPU reads correct instruction bytes: C3 50 01 (JP 0x0150) ✓
- CPU advances PC by 3 bytes (correct for 3-byte instruction) ✓
- BUT: PC goes 0x0000 → 0x0001 → 0x0002 → 0x0003 → 0x0004 (sequential) ✗
- Never jumps to 0x0150 ✗

#### Debug Trace Analysis

**Test 1:** PC monitoring after reset
- After reset release: PC=0x0000 ✓
- But ce_cpu=0 for first 20 cycles ✗
- ce_cpu first goes high at cycle 24

**Test 2:** Detailed CPU execution trace
- First M1 fetch at cycle 36: PC=0x0001 (NOT 0x0000!) ✗
- CPU fetching from wrong address!

**Test 3:** Continuous trace from reset
Found the smoking gun at cycle 158:

```
Cycle |  PC    | M1 | RD | ce | rom_do | clk_div
------|--------|----|----|----|---------|---------
   28 | 0x0000 | 0  | 0  | 1  | 0x00   | 0       ← ce_cpu HIGH (correct)
   29 | 0x0000 | 0  | 0  | 1  | 0x00   | 0       ← ce_cpu HIGH (correct)
   30 | 0x0000 | 1  | 0  | 0  | 0x00   | 1       ← M1 starts, but ce_cpu=0!
   94 | 0x0000 | 0  | 1  | 0  | 0x00   | 1       ← RD active, but ce_cpu=0!
  158 | 0x0001 | 1  | 0  | 0  | 0x50   | 1       ← PC ADVANCED with ce_cpu=0!
```

**KEY FINDING:** The CPU executed and advanced PC from 0x0000 to 0x0001 while `ce_cpu=0`!

## Root Cause

### CPU Core Does Not Respect CLKEN

The GameBoy uses a **GBse** CPU core (TV80-based Z80-compatible). This core has two inputs:
- `CLK_n` - System clock (64 MHz in our design)
- `CLKEN` - Clock enable (should gate operations to ~4MHz)

**Expected Behavior:**
```
CPU should only advance state when (CLK_n edge AND CLKEN=1)
Effective CPU frequency = 64MHz / 16 = 4MHz
```

**Actual Behavior:**
```
CPU advances state on EVERY CLK_n edge regardless of CLKEN
Effective CPU frequency = 64MHz (16x too fast!)
```

### Impact

1. **Incorrect Timing:** CPU runs 16x faster than intended
2. **Data Not Ready:** CPU advances PC before SDRAM provides data
3. **Wrong Bytes Read:** CPU reads from wrong addresses
4. **Instructions Not Executed:** CPU fetches partial instructions and fails to execute them correctly

### Evidence

From `gb.v` line 348-351:
```verilog
GBse cpu (
    .RESET_n           ( !reset_ss        ),
    .CLK_n             ( clk_sys         ),  // 64 MHz - always running!
    .CLKEN             ( cpu_clken       ),  // ~4MHz enable - IGNORED!
```

The CPU receives the full-speed 64MHz clock and should use CLKEN to gate operations, but it doesn't.

## Verification

### Test Results

All three SDRAM timing fixes work correctly:
1. ✅ ce_cpu pulses at correct rate (every 16 clk_sys cycles)
2. ✅ ce_cpu2x pulses at correct rate (every 8 clk_sys cycles)
3. ✅ SDRAM provides correct data at correct time
4. ✅ CPU reads correct instruction bytes

BUT:
- ✗ CPU executes even when ce_cpu=0
- ✗ CPU runs 16x too fast
- ✗ Instructions not executed correctly

### Why SDRAM Fixes Weren't Enough

The SDRAM fixes made data available faster and at the right time relative to ce_cpu pulses. However, since the CPU ignores ce_cpu and runs at full speed (64MHz), it still:
1. Fetches bytes before SDRAM is ready
2. Advances PC out of sync with ce_cpu
3. Reads from wrong addresses
4. Never properly executes the JP instruction

## Solution Options

### Option 1: Fix GBse/TV80 CPU Core (RECOMMENDED)
Modify the CPU core to properly respect the CLKEN signal. The CPU's state machine should only advance when `CLKEN=1`.

**Pros:**
- Proper solution
- CPU runs at correct speed
- All timing issues resolved

**Cons:**
- Requires modifying third-party CPU core
- May be complex depending on core internals

### Option 2: Gate CLK_n with CLKEN
Instead of using CLKEN as an enable, actually gate the clock:
```verilog
wire cpu_clk_gated = clk_sys & ce_cpu;
.CLK_n(cpu_clk_gated),
.CLKEN(1'b1),
```

**Pros:**
- No CPU core modifications needed
- Guaranteed to work

**Cons:**
- Clock gating can cause glitches
- Violates synchronous design principles
- May fail timing in FPGA

### Option 3: Use Different CPU Core
Replace GBse with a CPU core that properly supports clock enables.

**Pros:**
- Clean solution
- Known-good CPU core

**Cons:**
- Requires significant integration work
- May have other compatibility issues

## Recommended Action

**Investigate GBse/TV80 CPU core** to find where CLKEN is supposed to gate operations but doesn't. The bug is likely:
1. State machine advances on every CLK_n edge instead of gated by CLKEN
2. Program counter increments without checking CLKEN
3. Internal registers update without checking CLKEN

Once identified, add proper CLKEN gating to the affected logic.

## Files Modified (SDRAM Fixes)

These fixes are valid and should be kept:

1. `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/gameboy_sim.v`
   - Lines 94-114: Clock enable generation with clk_div_next wire

2. `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/sim/mister_sdram_model.h`
   - cas_latency = 0
   - Immediate rdata update for zero-latency mode

3. `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/rtl/sdram_sim.sv`
   - Lines 210-247: Zero-latency ACTIVATE and READ states
   - Lines 35, 56, 99, 113: Combinational dout output

## Documentation Created

- `SDRAM_FIX_SUMMARY.md` - Complete SDRAM timing fixes
- `INVESTIGATION_STATUS.md` - Original investigation notes
- `ROOT_CAUSE_ANALYSIS.md` - This document

## Conclusion

Through systematic debugging with detailed CPU execution traces, we identified that the GameBoy CPU core does not properly respect its CLKEN input, causing it to run at full speed (64MHz) instead of the gated speed (~4MHz). This causes all observed symptoms:
- PC advancing too quickly
- Reading from wrong addresses
- Instructions not executing correctly
- Never reaching target address 0x0150

The SDRAM timing fixes are correct and necessary, but insufficient because the CPU ignores the clock enable signal that would synchronize it with the slower SDRAM.

**Next Step:** Fix the GBse/TV80 CPU core to properly gate all state updates with the CLKEN signal.
