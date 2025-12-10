# GameBoy SDRAM Investigation - Current Status

## Problem Statement

GameBoy CPU fails to execute JP instruction correctly - jumps to 0x01C3 instead of 0x0150. This prevents the test ROM from reaching the LCD control register write code at address 0x0150.

## Progress Summary

### ✅ Issues Fixed

1. **Clock enable during reset** (gameboy_sim.v)
   - Clock divider now runs during reset
   - ce_cpu signal properly generated from start

2. **ioctl_addr double-shifting** (test_simple_lcd.cpp)
   - Was being shifted in C++ AND RTL
   - Fixed: Pass byte address directly, RTL handles word conversion

3. **SDRAM rdata persistence** (mister_sdram_model.h + test_simple_lcd.cpp)
   - C++ model was clearing rdata every cycle
   - Fixed: Made sdram_rdata global/persistent across processSDRAM calls

4. **SDRAM CAS latency** (mister_sdram_model.h)
   - Set cas_latency = 0 for simulation
   - Added immediate rdata update when CMD_READ is issued

### ⚠️ Remaining Issue: One-Transaction Delay

**Observation:**
The SDRAM controller exhibits a consistent one-transaction delay - each read returns data from the PREVIOUS transaction:

```
Read #1: Address 0x000000 → Returns 0x50C3 ✓ (correct)
Read #2: Address 0x000000 → Returns 0x50C3 ✓ (duplicate, correct)
Read #3: Address 0x000002 → Returns 0x50C3 ✗ (WRONG - old data!)
Read #4: Address 0x000002 → Returns 0x0001 ✓ (correct, but one transaction late)
```

**Impact:**
- CPU at PC=0x0002 reads byte 0xC3 (opcode from PC=0x0000) instead of 0x01
- CPU jumps to 0x01C3 instead of 0x0150
- Never reaches LCD enable code at 0x0150

## Root Cause Analysis

### C++ SDRAM Model - ✅ Working Correctly

**Verified:**
- Reads correct data from memory (0x50C3 at address 0x000000, 0x0001 at address 0x000002)
- Updates `rdata` immediately when `CMD_READ` is issued (cas_latency=0)
- Passes updated data to RTL via `sd_data_in`

**Evidence:**
```
SDRAM: READ bank=0 addr=0x000000 data=0x50C3  ← Correct
SDRAM: READ bank=0 addr=0x000002 data=0x0001  ← Correct
```

### RTL SDRAM Controller - ⚠️ Issue Identified

**Problem:** The RTL's `dout` register (which drives `sdram_do`) is not updating when expected.

**Expected Behavior:**
```verilog
// sdram_sim.sv lines 236-243
READ: begin
    cycle <= cycle + 1;
    if (cycle >= 2) begin
        dout <= sd_data_in;  // Should sample sd_data_in
        state <= PRECHARGE;
    end
end
```

**Timeline for Third Read (address 0x000002):**
- Cycle 232: CMD_READ issued
  - C++ model: reads memory[2] = 0x01, memory[3] = 0x00 → rdata = 0x0001
  - C++ model: sd_data_in = 0x0001 (updated immediately)
- Cycle 248: RTL samples
  - State=READ, cycle=2
  - `dout <= sd_data_in` executed
  - **Expected**: dout = 0x0001
  - **Actual**: sdram_do still shows 0x50C3

**Measurement:**
- First unique read completes at cycle 74: sdram_do = 0x50C3 ✓
- Second unique read samples at cycle 248: sdram_do = 0x50C3 ✗
- Data finally appears at cycle 408: sdram_do = 0x0001 (one transaction late)

## Hypotheses for RTL Issue

### Hypothesis 1: Timing of `dout <= sd_data_in`

The non-blocking assignment `dout <= sd_data_in` schedules the update for the END of the clock cycle. If something else is interfering with this update, or if the GameBoy core is sampling `sdram_do` BEFORE the update takes effect, we'd see stale data.

### Hypothesis 2: `sd_data_in` Not Stable

The C++ model updates `rdata` during `processSDRAM()` which is called AFTER `top->eval()`. If the RTL samples `sd_data_in` during eval() but before processSDRAM() updates it, we'd see old data.

**But:** We already tried calling processSDRAM() before eval(), and that made things worse (all zeros).

### Hypothesis 3: Duplicate Reads Causing Confusion

The RTL does duplicate reads of the same word address (because the CPU reads sequential bytes):
- Read address 0x000000 twice (for bytes 0 and 1)
- Read address 0x000002 twice (for bytes 2 and 3)

Perhaps the duplicate reads are somehow causing the `dout` register to not update properly between unique addresses.

## Next Steps

1. **Add VCD waveform tracing** to see exact timing of signals:
   - When does `sd_data_in` change?
   - When does `dout` update?
   - When does the GameBoy core sample `sdram_do`?

2. **Check if `dout` assignment is being overridden** somewhere else in the RTL

3. **Verify ce_cpu2x timing** - confirm state machine advances when we think it does

4. **Test with simplified ROM** that doesn't require sequential byte reads (word-aligned accesses only)

## Files Modified

- `mister_sdram_model.h` - Set cas_latency=0, immediate rdata update
- `test_simple_lcd.cpp` - Made sdram_rdata persistent, removed double eval
- `gameboy_sim.v` - Clock enable fix (from previous session)

## Documentation Created

- `CPU_COMPARISON_ANALYSIS.md` - TV80 vs T80 CPU analysis
- `SDRAM_LATENCY_BUG_ANALYSIS.md` - Detailed timing analysis
- `SDRAM_TIMING_FIX.md` - CAS latency fix documentation
- `INVESTIGATION_STATUS.md` - This file

## Test ROM Layout

```
0x0000: 0xC3  (JP opcode)
0x0001: 0x50  (low byte of address → target should be 0x0150)
0x0002: 0x01  (high byte of address)
0x0150: F3 3E 91 E0 40 18 FE  (Disable interrupts, LD A,0x91, LDH (0x40),A, JR -2)
```

**Expected Execution:**
1. PC=0x0000: Read 0xC3 (JP opcode)
2. PC=0x0001: Read 0x50 (low byte)
3. PC=0x0002: Read 0x01 (high byte)
4. Jump to 0x0150
5. Write 0x91 to LCDC register

**Actual Execution:**
1. PC=0x0000: Read 0xC3 (JP opcode) ✓
2. PC=0x0001: Read 0x50 (low byte) ✓
3. PC=0x0002: Read 0xC3 (WRONG - opcode from PC=0x0000!) ✗
4. Jump to 0x01C3 (wrong address)
5. Never reaches LCDC write code

## Conclusion

We've successfully fixed the C++ SDRAM model timing, but there's a persistent one-transaction delay in the RTL's `dout` register updates. The issue appears to be in the SDRAM controller RTL (`sdram_sim.sv`) or in how the GameBoy core samples the data, not in the C++ model.

Further investigation with VCD waveform tracing is recommended to pinpoint the exact timing issue.
