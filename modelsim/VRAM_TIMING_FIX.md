# CGA VRAM Read/Write Testbench Timing Fix

## Problem

The CGA integration test was failing on the VRAM read/write test with:
- **Symptom**: Reads returned undefined values (0xxxxx) even after writes
- **Root Cause**: Race condition in testbench timing

## Investigation

### Initial Symptoms
```
Test: VRAM read/write
  Writing 0xAA55 to VRAM address 0x3000
  Read back: 0xxxxx
  [FAIL] VRAM mismatch - wrote 0xAA55, read 0xxxxx
```

### Debug Process

1. **Added debug prints** to VRAM and busConverter modules
2. **Discovered**: No write operations were happening - only reads
3. **Traced signals**: busConverter was seeing `we=0` during write operations
4. **Identified race condition**: Testbench signals were not stable when sampled

### Root Cause Analysis

The testbench tasks were structured as:
```systemverilog
@(posedge clock);  // Wait for clock edge
memaccess = 1'b1;  // Set signals after clock edge
imem_m_wr_en = 1'b1;
...

@(posedge clock);  // Next clock edge - busConverter samples here
```

**The Problem**:
- Both testbench and busConverter's `always @(posedge clock)` blocks trigger at the same clock edge
- This creates a **race condition** - the order of execution is non-deterministic
- busConverter was sampling signals BEFORE the testbench set them, getting old values

**Evidence from Debug**:
```
busConverter @clk: state=0, en=1, we=0, bytesel=11, addr=0x0000
                                    ^^^ Should be 1!      ^^^ Should be 0x3000!
```

## Solution

### Fix Applied

Modified all testbench tasks to add a small delay after clock edges:

```systemverilog
task write_vram_word(input [15:0] addr, input [15:0] data);
    begin
        @(posedge clock);
        #1;  // Small delay to avoid race with always @(posedge clock) blocks
        memaccess = 1'b1;
        imem_m_addr = addr[19:1];
        imem_m_data_in = data;
        imem_m_bytesel = 2'b11;
        imem_m_wr_en = 1'b1;

        @(posedge clock);  // Now busConverter samples stable signals
        wait(mem_m_ack);
        ...
    end
endtask
```

### Files Modified

**Testbenches:**
- `modelsim/cga_controller_integration_tb.sv` - Added `#1` delays to:
  - `write_cga_register()` task (line 113)
  - `read_cga_register()` task (line 134)
  - `write_vram_word()` task (line 152)
  - `read_vram_word()` task (line 173)

- `modelsim/vram_debug_tb.sv` - Minimal debug testbench (NEW)
  - Used to isolate and debug the timing issue

## Verification

### Before Fix:
```
Total Tests: 6
Passed:      5
Failed:      1
Success Rate: 83%

[FAIL] VRAM read/write - Read data (0xxxxx) != written data (0xAA55)
```

### After Fix:
```
Total Tests: 6
Passed:      6
Failed:      0
Success Rate: 100%

✓✓✓ SUCCESS: All CGA controller tests passed! ✓✓✓

Verified functionality:
  - CRTC register access
  - VRAM read/write ✓ (FIXED!)
  - All 7 CGA video modes
  - Video signal generation
```

## Key Lessons

1. **Testbench Timing Matters**: Even in simulation, proper setup/hold times must be respected
2. **Race Conditions**: When multiple `always @(posedge clock)` blocks exist, avoid setting and sampling signals at the same edge
3. **Debug Strategy**: Adding targeted debug prints helped identify that the problem was NOT in the hardware modules, but in the testbench timing
4. **Isolation**: Creating a minimal testbench (`vram_debug_tb.sv`) helped isolate the issue from other complexities

## Technical Details

### Why the `#1` Delay Works

The `#1` delay ensures signals are set in a different simulation time slot from when they're sampled:

```
Time T:   Clock edge → Testbench wakes → Waits 1ns
Time T+1: Testbench sets signals (stable now)
Time T+20: Next clock edge → busConverter samples stable signals ✓
```

### Alternative Solutions

Other valid approaches:
1. **Non-blocking assignments** in testbench (but blocking is more readable for tasks)
2. **Separate always blocks** to drive signals (more complex)
3. **Use initial blocks** with absolute timing (less flexible)

The `#1` delay solution is:
- Simple and clear
- Commonly used in testbenches
- Doesn't affect synthesis (testbench only)
- Prevents race conditions reliably

## Impact

- **CGA Controller**: Now 100% functional (all 6 integration tests passing)
- **VRAM Access**: Verified working for both read and write operations
- **Test Coverage**: Complete validation of CGA controller hardware

---

**Date**: November 8, 2025
**Status**: FIXED ✓
**Test Results**: 6/6 passing (100%)
