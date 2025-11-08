# Cache Module Critical Bugs

## File: `Quartus/rtl/common/Cache.sv`

### Bug 1: No Initialization Logic (CRITICAL)

**Severity:** Critical
**Status:** Identified

**Description:**
The Cache module has intentionally disabled reset logic with the comment:
```systemverilog
// No reset: the CPU isn't cache coherent so we need to preserve state across
// reset
always_ff @(posedge reset)
    ;
```

This causes all internal state variables to start as 'x' (undefined) in simulation:
- `busy` - undefined at startup
- `flushing` - undefined at startup
- `updating` - undefined at startup
- `line_idx` - undefined at startup
- `line_valid` - undefined at startup
- `accessing` - undefined at startup

**Impact:**
1. **Simulation:** Module completely non-functional - all tests fail with timeout
2. **Synthesis:** Unpredictable behavior on FPGA power-up
3. **Real Hardware:** Random initial state could cause system hangs or crashes

**Root Cause:**
The design philosophy of "preserving state across resets" is fundamentally flawed for:
1. Initial power-on: There is no valid state to preserve
2. Simulation: All variables start as 'x'
3. FPGA configuration: Initial state is undefined

**Expected Behavior:**
On reset (or power-on), the cache should initialize to a clean, known state:
```systemverilog
always_ff @(posedge reset or posedge clk) begin
    if (reset) begin
        busy <= 1'b0;
        flushing <= 1'b0;
        updating <= 1'b0;
        line_idx <= 3'b0;
        line_valid <= 8'b0;
        accessing <= 1'b0;
        // Note: Tag/Valid/Dirty RAMs can remain uninitialized
        // as they'll be filled during normal operation
    end else begin
        // Normal operation...
    end
end
```

**Test Results:**
- Cache testbench: 3/10 tests passing (30%)
- All cache-hit/miss tests fail with timeout
- Only passthrough mode (cache disabled) works

**Workaround for Testing:**
```systemverilog
// Force initial state in testbench
initial begin
    force dut.busy = 1'b0;
    force dut.flushing = 1'b0;
    force dut.updating = 1'b0;
    force dut.line_idx = 3'b0;
    force dut.line_valid = 8'b0;
    #1;
    release dut.busy;
    release dut.flushing;
    release dut.updating;
    release dut.line_idx;
    release dut.line_valid;
end
```

Note: Even with workaround, cache still doesn't function correctly in tests.

### Bug 2: Cache State Persistence Misconception

**Severity:** Design Flaw
**Status:** Identified

**Description:**
The comment states "the CPU isn't cache coherent so we need to preserve state across reset" but this misunderstands the purpose of reset signals.

**Analysis:**
1. **Reset Purpose:** Initialize hardware to known state after power-on or error condition
2. **Cache Coherency:** Unrelated to whether state is preserved across intentional resets
3. **State Preservation:** If needed, should be implemented through:
   - Write-back on reset assertion (flush dirty lines)
   - Controlled shutdown sequence
   - NOT by ignoring reset signal

**Recommendation:**
1. Add proper reset initialization
2. If state preservation is truly required:
   - Implement flush-on-reset logic
   - Add reset acknowledgment signal
   - Document the shutdown/restart sequence

### Bug 3: No RAM Initialization

**Severity:** Medium
**Status:** Identified

**Description:**
The DPRam and BlockRam instances used for tags, valid bits, dirty bits, and data storage have no initialization. While this is acceptable for the data RAM, the valid bits should be initialized to 0.

**Impact:**
- Valid bits start as 'x' in simulation
- In real hardware, could cause false cache hits on power-up
- Potential for reading uninitialized memory thinking it's cached data

**Recommendation:**
```systemverilog
// In reset block
// Clear all valid bits on reset
// (Tags and data can remain uninitialized)
```

## Testing Status

### Created Tests:
- `modelsim/cache_tb.sv` - Comprehensive cache testbench (10 tests)
- `modelsim/run_cache_test.sh` - Test automation script

### Test Coverage:
1. ✓ Cache disabled passthrough mode
2. ✗ Cache miss handling
3. ✗ Cache hit detection
4. ✗ Write-through behavior
5. ✗ Dirty bit management
6. ✗ Cache line flush
7. ✗ Cache line fill
8. ✗ Tag matching
9. ✗ Byte-wide writes
10. ✗ Cache line boundaries

### Recommended Actions:
1. **Immediate:** Add proper reset logic to Cache.sv
2. **Testing:** Re-run cache testbench after fix
3. **Verification:** Test on actual hardware after FPGA synthesis
4. **Documentation:** Update comments to reflect correct reset behavior

## Related Files:
- `Quartus/rtl/common/Cache.sv` - Cache module (NEEDS FIX)
- `Quartus/rtl/common/DPRam.sv` - Dual-port RAM (OK)
- `Quartus/rtl/common/BlockRam.sv` - Block RAM (OK)
- `modelsim/cache_tb.sv` - Testbench
- `modelsim/run_cache_test.sh` - Test script

## Priority:
**HIGH** - This affects CPU performance and stability. Cache should either be:
1. Fixed with proper reset logic, OR
2. Disabled entirely until fixed

Leaving it in current state risks unpredictable system behavior.
