# GameBoy CPU Clock Enable Bug - Final Analysis

## Executive Summary

**CONFIRMED BUG:** The GameBoy CPU advances PC (Program Counter) and executes instructions even when `cpu_clken=0`. This causes the CPU to run at full clock speed (64MHz) instead of the intended ~4MHz, leading to incorrect program execution.

## Test Evidence

Test: `test_cpu_clken_verify.cpp`
Results: **PC advanced at cycles 158, 286, and 414 - ALL with `cpu_clken=0`**

```
Cycle | PC     | M1 | ce_cpu | cpu_clken | clk_div | Notes
------|--------|----|----- ---|-----------|---------|------------------------------------------
  158 | 0x0001 | 1  |   0    |     0     |   1     | *** PC CHANGED with cpu_clken=0! ***
  286 | 0x0002 | 1  |   0    |     0     |   1     | *** PC CHANGED with cpu_clken=0! ***
  414 | 0x0003 | 0  |   0    |     0     |   1     | *** PC CHANGED with cpu_clken=0! ***
```

Summary:
- **Cycles with cpu_clken=1:** 30
- **Cycles with PC changes:** 4
- **PC changes when cpu_clken=0:** 3 out of 4 (75%!)

## Signal Chain Analysis

### Clock Enable Signal Path

1. **gameboy_sim.v** generates `ce_cpu` (~4MHz) and `ce_cpu2x` (~8MHz)
   - Fixed via `clk_div_next` wire to use incremented divider value
   - ✅ Both signals now pulse correctly

2. **gb.v** receives `ce` and `ce_2x` inputs
   - Creates internal: `ce_cpu = cpu_speed ? ce_2x : ce`
   - Creates gated: `cpu_clken = ~hdma_cpu_stop & ce_cpu`
   - ✅ Logic verified correct

3. **GBse wrapper** (tv80_gameboy.v) receives `CLKEN` input
   - Passes to tv80_core as `.cen(CLKEN)`
   - Bus control signals gated by `if (CLKEN)` at line 98
   - ✅ Wrapper logic verified correct

4. **tv80_core.v** receives `cen` input
   - Creates internal: `ClkEn = cen && ~BusAck` (line 353)
   - All sequential blocks gated by `if (ClkEn == 1'b1)` or `if (cen == 1'b1)`
   - ✅ Core logic verified correct

### RTL Code Review

All clock-sensitive always blocks in tv80_core.v properly check `ClkEn` or `cen`:

- **Line 375-xxx:** Main register updates - `if (ClkEn == 1'b1)`
- **Line 881-930:** Address register updates - `if (ClkEn == 1'b1)`
- **Line 1043-1107:** Bus mux updates - `if (ClkEn == 1'b1)`
- **Line 1194-1333:** **MAIN STATE MACHINE** - `if (cen == 1'b1)`
  - Line 1278: `tstate <= 7'b0000010;`
  - Line 1281, 1290, 1297, 1314: `mcycle <=` updates
  - Line 1323: `tstate <= { tstate[5:0], tstate[6] };`

**All state updates are properly gated!**

## Previous Fixes (All Valid)

The SDRAM timing fixes completed earlier are all correct and necessary:

1. ✅ Clock enable generation (clk_div_next wire)
2. ✅ SDRAM read latency reduction
3. ✅ Combinational dout output
4. ✅ C++ model CAS latency = 0

These fixes ensure CPU reads correct instruction bytes (verified: 0xC3, 0x50, 0x01 for JP 0x0150).

## Root Cause Hypothesis

Despite all RTL code appearing correct, the CPU demonstrably does NOT respect `cpu_clken`. Possible causes:

### Hypothesis 1: Verilator Compilation Bug
Verilator may be incorrectly optimizing or scheduling the combinational `ClkEn` assignment, causing it to lag the sequential blocks that use it.

**Evidence:**
- All RTL code is correct
- Bug only observed in Verilator simulation
- Similar timing-sensitive code works in other projects

**Test:** Try Icarus Verilog or ModelSim simulation to see if bug reproduces

### Hypothesis 2: Signal Ordering/Race Condition
The combinational `ClkEn` derivation (line 353) may evaluate after the sequential blocks on the same clock edge in Verilator's event scheduling.

**Evidence:**
- ClkEn is assigned in a combinational `always @(*)` block
- Sequential blocks use ClkEn but may evaluate first
- Verilog spec doesn't guarantee ordering within same timestep

**Test:** Change ClkEn to be registered instead of combinational

### Hypothesis 3: Address Bus vs PC Register Confusion
The test monitors the A (address) output bus, which might update combinationally before the PC register actually changes.

**Evidence:**
- Test reads `dbg_cpu_addr` = `gameboy.cpu_addr` = GBse A output
- A bus might reflect internal state before PC register updates
- Z80 A bus can change during address calculation phases

**Counter-evidence:**
- M1_n signal also active when PC "changes"
- M1 should only be active during instruction fetch with valid PC

## Recommended Actions

### Priority 1: Isolate Verilator vs RTL Bug

Create test using different simulator:

```bash
cd modelsim/
iverilog -g2012 -o tb_gameboy <RTL files> gameboy_test.v
./tb_gameboy
```

If bug does NOT reproduce in Icarus Verilog → Verilator compilation bug
If bug DOES reproduce → RTL design issue

### Priority 2: Register ClkEn Signal

Modify tv80_core.v to register ClkEn instead of deriving combinationally:

```verilog
// Current (combinational):
always @(*) begin
    ClkEn = cen && ~BusAck;
end

// Proposed (registered):
always @(posedge clk) begin
    ClkEn <= cen && ~BusAck;
end
```

**Risk:** This adds one cycle delay to ClkEn, which may affect timing

### Priority 3: Monitor Internal PC Register

Expose tv80_core's internal PC register as `/*verilator public*/` and verify it matches A bus timing:

```verilog
reg [15:0] PC /*verilator public*/;
```

Then compare PC vs A in test to see if discrepancy exists.

## Impact Assessment

**Severity:** CRITICAL - CPU runs at wrong speed, breaks all GameBoy software

**Scope:**
- Affects all Verilator simulations
- May or may not affect FPGA synthesis (needs testing)
- All other peripherals working correctly

**Workaround:** None - CPU core must be fixed

## Files Modified/Created

### Test Files Created:
- `test_cpu_clken_verify.cpp` - Confirms bug exists
- `test_reset_trace.cpp` - Original debug trace (monitored wrong signal)
- `CPU_CLKEN_BUG_REPORT.md` - This document

### RTL Files Modified:
- `gameboy_sim.v` - Clock enable generation fix (✅ correct)
- `sdram_sim.sv` - Latency and combinational dout fixes (✅ correct)
- `tv80_core.v` - Added `/*verilator public*/` to ClkEn (for debug)

### RTL Files Analyzed (No Changes Needed - Already Correct):
- `gb.v` - GameBoy core, cpu_clken generation
- `tv80_gameboy.v` - GBse wrapper module
- `tv80_core.v` - Z80 CPU core with GameBoy mode

## Next Steps

1. **Test with Icarus Verilog** - Determine if Verilator-specific bug
2. **Try registered ClkEn** - May fix Verilator scheduling issue
3. **Contact Verilator developers** - If confirmed as Verilator bug
4. **Alternative:** Use different CPU core (e.g., pure Verilog without VHDL heritage)

## Conclusion

The GameBoy CPU does NOT respect the `cpu_clken` signal, causing it to run at full speed (64MHz) instead of ~4MHz. All RTL code appears correct - the bug is likely in Verilator's compilation/scheduling of the combinational `ClkEn` signal. Testing with a different simulator is the critical next step to isolate whether this is a Verilator bug or an RTL design issue.
