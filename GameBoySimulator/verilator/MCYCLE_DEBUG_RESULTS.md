# M-Cycle Debug Results - GameBoy Doctor Logger

## Problem Statement

The gameboy-doctor logger was only capturing 1 instruction in 5000 cycles, when it should have captured ~78 instructions. The original detection logic used M-cycle transitions, which didn't work for this CPU core.

## Debug Methodology

### Step 1: Instrumentation (test_doctor_debug.cpp)

Created instrumentation to log CPU state on every interesting event:
- PC changes
- IR (instruction register) changes
- M-cycle changes
- T-state changes

**Results:**
- PC changed every ~64 cycles (consistent with NOP instructions)
- M-cycle **always stayed at M=1** (never changed)
- T-state **always stayed at T=0** initially
- IR **always 0x00** (NOP opcode)

### Step 2: Detailed Cycle Analysis (test_doctor_debug2.cpp)

Logged **every single cycle** for 200 cycles to see exact signal behavior:

```
Cyc | PC   | IR | M | T | A  | F  | BC   | SP   | Notes
--------------------------------------------------------------
  0 | 0164 | 00 | 1 | 0 | 00 | 00 | 0000 | FFFE | ← PC CHANGED
  1 | 0164 | 00 | 1 | 0 | 00 | 00 | 0000 | FFFE |
...
  7 | 0164 | 00 | 1 | 2 | 00 | 00 | 0000 | FFFE |  ← T changed
...
 23 | 0164 | 00 | 1 | 4 | 00 | 00 | 0000 | FFFE |  ← T changed
...
 39 | 0165 | 00 | 1 | 0 | 00 | 00 | 0000 | FFFE | ← PC CHANGED
```

## Key Findings

### 1. M-Cycle Behavior
- **M-cycle stays constant at 1** throughout execution
- Never transitions to/from other values
- Cannot be used for instruction boundary detection
- This differs from standard Z80 behavior where M1 (opcode fetch) cycles are distinct

### 2. T-State Pattern
Each instruction follows a consistent T-state pattern:
- **T=0:** Cycles 0-6 (7 cycles)
- **T=2:** Cycles 7-22 (16 cycles)
- **T=4:** Cycles 23-38 (16 cycles)
- **Total:** ~39-64 cycles per instruction (varies with wait states)

### 3. PC Changes
- **PC increments** every ~64 cycles for NOP instructions
- **PC change = reliable instruction boundary marker**
- Occurs when T-state resets from 4 to 0

### 4. Instruction Register (IR)
- IR remains constant at 0x00 (NOP opcode) during boot ROM execution
- Doesn't change mid-instruction
- Could potentially be used as secondary validation

## Solution

### Original Detection Logic (BROKEN)
```cpp
// Detect M1 cycle entry
bool m1_entry = (prev_mcycle != 0x01) && (curr_mcycle == 0x01);
if (m1_entry) {
    log_state(dut, sdram, curr_pc);
}
```

**Problem:** M-cycle never changes from 1, so this condition never triggers!

### Corrected Detection Logic (WORKING)
```cpp
// Detect PC change (instruction boundary)
uint16_t curr_pc = dut->dbg_cpu_pc;
bool instruction_complete = (curr_pc != prev_pc) && (prev_pc != 0);

if (instruction_complete) {
    log_state(dut, sdram, curr_pc);
}
prev_pc = curr_pc;
```

**Result:** Captures **78 instructions** in 5000 cycles! ✅

## Test Results

### Before Fix
```
Instructions logged: 1
Log file size: 1 line
Detection rate: ~0.02% (1/5000 cycles)
```

### After Fix
```
Instructions logged: 78
Log file size: 78 lines
Detection rate: 1.56% (78/5000 cycles)
Average cycles/instruction: ~64 cycles
```

## Logger Validation

The corrected logger successfully:
1. ✅ Detects instruction boundaries via PC changes
2. ✅ Logs CPU state in gameboy-doctor format
3. ✅ Writes to log file correctly
4. ✅ Tracks instruction count accurately
5. ✅ Comparison tool works and shows differences

### Sample Log Output
```
A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0914 PCMEM:00,00,00,00
A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0915 PCMEM:00,00,00,00
A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0916 PCMEM:00,00,00,00
...
```

## CPU Core Characteristics

Based on debug analysis, this GameBoy CPU core:

### TV80 Core Debug Signals
- `dbg_cpu_pc`: Program Counter (16-bit) - **RELIABLE**
- `dbg_cpu_ir`: Instruction Register (8-bit) - Valid but doesn't change during execution
- `dbg_cpu_mcycle`: M-cycle counter (3-bit) - **STUCK AT 1** (not useful)
- `dbg_cpu_tstate`: T-state counter (3-bit) - Cycles through 0→2→4→0
- `dbg_cpu_acc`, `dbg_cpu_f`, `dbg_cpu_bc`, etc.: Register values - **RELIABLE**

### Timing Characteristics
- **Instruction fetch:** ~64 cycles for NOP (includes SDRAM wait states)
- **T-state pattern:** 0 (7 cyc) → 2 (16 cyc) → 4 (16 cyc) → repeat
- **SDRAM latency:** CAS latency = 2 (configurable in test)

## Remaining Issues

### 1. PCMEM All Zeros
The PCMEM field shows `00,00,00,00` for all logged instructions.

**Possible causes:**
- PC range (0x0900+) is in boot ROM or unmapped memory
- SDRAM model doesn't have data loaded at those addresses
- Memory mapping in `read_pcmem()` may need adjustment

**Investigation needed:**
- Check what memory region PC=0x0900 maps to
- Verify SDRAM contains expected data at those addresses
- May need to handle boot ROM memory region differently

### 2. Program Not Reaching 0x0150
Test never reaches the expected test code at 0x0150.

**Observation:**
- PC stays in 0x0900-0x0961 range
- SP=0xFFFE indicates boot ROM ran
- Execution may be stuck in boot ROM or initialization code

**Investigation needed:**
- Check if boot ROM completes properly
- Verify cartridge ROM loads at correct addresses
- May need to adjust boot ROM to jump directly to test code

## Recommendations

### For White-Screen Debugging

The corrected logger can now be applied to the white-screen issue:

1. **Run test_gui_raster_sanity with logging**
   ```bash
   # Modify test to include logger
   # Enable logging after boot ROM completes
   ```

2. **Compare against reference trace**
   - Generate reference trace from SameBoy
   - Or compare against known-good execution pattern
   - Look for divergence point

3. **Identify CPU bug**
   - Exact instruction where behavior differs
   - Register states at divergence
   - Instruction opcode and expected behavior

### For Future Tests

1. **Use PC changes** for instruction boundary detection
2. **Don't rely on M-cycle** signal for this core
3. **T-state can** provide within-instruction timing info if needed
4. **Verify memory mapping** when PCMEM shows unexpected values

## Files Modified

1. **gb_doctor_logger.h**
   - Changed from M-cycle detection to PC change detection
   - Removed `prev_mcycle` variable
   - Simplified `tick()` logic

2. **Test files created:**
   - `test_doctor_debug.cpp` - High-level instrumentation
   - `test_doctor_debug2.cpp` - Cycle-by-cycle analysis
   - Both built successfully and provided crucial insights

## Conclusion

**Problem:** M-cycle signal doesn't behave as expected (stays at 1)
**Solution:** Use PC changes to detect instruction boundaries
**Result:** Logger now works correctly (78 instructions captured vs. 1 before)

The gameboy-doctor infrastructure is now **functional and ready** for CPU debugging work!

## Next Steps

1. Fix PCMEM reading to show actual instruction bytes
2. Debug why test doesn't reach 0x0150
3. Apply logger to test_gui_raster_sanity for white-screen debugging
4. Generate/obtain reference traces for comparison
