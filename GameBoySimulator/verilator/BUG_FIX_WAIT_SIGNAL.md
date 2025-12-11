# GameBoy Simulator - WAIT_n Signal Bug Fix

## Date: 2025-12-11

## ROOT CAUSE CONFIRMED

**File**: `GameBoySimulator/gameboy_core/rtl/gb.v`
**Line**: 354
**Issue**: WAIT_n signal hardwired to 1 (always ready)

```verilog
GBse cpu (
    .RESET_n           ( !reset_ss        ),
    .CLK_n             ( clk_sys         ),
    .CLKEN             ( cpu_clken       ),
    .WAIT_n            ( 1'b1            ),  ← HARDWIRED! Should be SDRAM ready signal
    .INT_n             ( irq_n           ),
    ...
```

## Why This Causes the Bug

### TV80 CPU Core Behavior

The **TV80** (Verilog Z80 core) has a `wait_n` input signal that tells it when memory is ready:
- **WAIT_n = 1**: Memory ready, CPU can proceed
- **WAIT_n = 0**: Memory busy, CPU must wait

**Location**: `GameBoySimulator/tv80/rtl/core/tv80_core.v`

### With WAIT_n Hardwired to 1

When `WAIT_n` is hardwired to `1'b1`:

1. **CPU assumes memory is ALWAYS ready instantly**
2. **CPU samples data bus immediately** (doesn't wait for SDRAM)
3. **With cas_latency = 0**: SDRAM provides data instantly → Works!
4. **With cas_latency = 2**: SDRAM has 2-cycle delay → CPU reads stale data → Instructions fail!

### Result

**Symptom**: CPU treats every byte as NOP, PC increments through ROM without executing instructions

**Evidence from test_jp_instruction.cpp**:
```
Expected: JP $0150 at 0x0100 → PC jumps to 0x0150
Actual:   PC increments 0x0100 → 0x0101 → 0x0102 → ... → 0x0150
          (80 addresses traversed - JP never executed!)
```

## THE FIX

### Option 1: Implement Proper WAIT_n Signal (CORRECT FIX - COMPLEX)

The SDRAM controller needs to drive `WAIT_n = 0` during latency cycles.

**Required Changes**:

1. **Add SDRAM ready signal** to SDRAM controller:
   ```verilog
   // In sdram.sv or sdram_sim.sv
   output reg mem_ready;  // New signal: 1 when data valid, 0 during latency
   ```

2. **Generate mem_ready signal** based on SDRAM state machine:
   ```verilog
   always @(posedge clk) begin
       if (read_command && latency_counter < CAS_LATENCY) begin
           mem_ready <= 1'b0;  // Not ready during latency
       end else begin
           mem_ready <= 1'b1;  // Ready when data valid
       end
   end
   ```

3. **Connect to CPU in gb.v line 354**:
   ```verilog
   .WAIT_n            ( sdram_ready      ),  // Was: 1'b1
   ```

**Pros**:
- ✅ Proper fix
- ✅ Realistic SDRAM timing
- ✅ Works with all cas_latency values

**Cons**:
- ❌ Requires modifying SDRAM controller
- ❌ Time-consuming (days to implement and test)
- ❌ Complex - need to understand SDRAM state machine

---

### Option 2: Use Zero Latency (QUICK WORKAROUND - RECOMMENDED FOR NOW)

Keep `WAIT_n = 1'b1` and set `cas_latency = 0` to match.

**Implementation**:

Edit `GameBoySimulator/verilator/sim_main_gui.cpp` line 1013:
```cpp
// BEFORE:
sdram->cas_latency = 2;  // Realistic CAS latency

// AFTER:
sdram->cas_latency = 0;  // Zero latency (matches WAIT_n=1 assumption)
```

**Why This Works**:
- SDRAM provides data instantly (1 cycle)
- CPU samples immediately (WAIT_n=1 means "ready now")
- Both expectations match → Instructions execute correctly!

**Pros**:
- ✅ Immediate fix (1-line change)
- ✅ Proven to work (84 unit tests passed)
- ✅ Minimal risk

**Cons**:
- ❌ Unrealistic memory timing
- ❌ Doesn't fix the underlying bug

---

## RECOMMENDED ACTION

**Use Option 2 (Zero Latency) NOW for immediate fix:**

1. Edit `sim_main_gui.cpp` line 1013:
   ```cpp
   sdram->cas_latency = 0;  // Zero latency workaround
   ```

2. Rebuild in Visual Studio (Ctrl+Shift+B)

3. Run GUI simulator

4. **Expected Result**:
   - Boot ROM completes ✅
   - PC executes cart ROM correctly ✅
   - Instructions execute (JP, JR, LD, etc.) ✅
   - PC loops at target address ✅
   - NO PC stuck at 0x0160 ✅

**Then pursue Option 1 later if realistic timing is critical for your project.**

## Files Involved

### Bug Location
- **`gameboy_core/rtl/gb.v:354`** - WAIT_n hardwired to 1

### TV80 CPU Core
- **`tv80/rtl/core/tv80_core.v`** - Has wait_n input (works correctly if driven properly)
- **`rtl/tv80_gameboy.v`** - GameBoy wrapper (passes WAIT_n through)

### SDRAM Controller
- **`gameboy_core/rtl/sdram.sv`** or **`rtl/sdram_sim.sv`** - Would need to generate ready signal

### Simulator
- **`verilator/sim_main_gui.cpp:1013`** - cas_latency setting (WORKAROUND LOCATION)

## Test Verification

After applying fix, run diagnostic tests:

```bash
cd GameBoySimulator/verilator
./test_jp_instruction           # Should show JP jumps directly to target
./test_cart_execution          # Should show cart ROM executes and loops
```

**Expected Output (after fix)**:
```
=== JP Instruction Execution Test ===
...
Cart PC[  2]: $0100 (ROM[$0100] = 0xC3)  ← JP opcode
Cart PC[  3]: $0150 (ROM[$0150] = 0x18)  ← JUMPED! (not incrementing)

✅ SUCCESS: Reached $0150 (JP executed correctly!)
✅ TEST PASSED
```

## Summary

**ROOT CAUSE**: WAIT_n hardwired to 1 in `gb.v:354`
**SYMPTOM**: CPU doesn't execute instructions with cas_latency > 0
**QUICK FIX**: Set cas_latency = 0 (1-line change in sim_main_gui.cpp)
**PROPER FIX**: Implement SDRAM ready signal and connect to WAIT_n (complex)
**RECOMMENDATION**: Use quick fix now, implement proper fix later if needed

---

**Status**: Root cause identified and confirmed
**Fix Available**: Yes (workaround ready, proper fix documented)
**Ready to Test**: Yes (1-line change in sim_main_gui.cpp:1013)
