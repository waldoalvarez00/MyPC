# GameBoy Cart ROM Bug - Complete Analysis

## Executive Summary

**Problem:** Nintendo logo doesn't display during boot ROM execution - screen stays white.

**Root Causes Found:**
1. ✅ **FIXED:** `dn_write` signal gated by `ce_cpu` preventing ioctl writes
2. ✅ **VERIFIED:** SDRAM write path working - data persists in memory
3. ❌ **ACTIVE BUG:** SDRAM controller not issuing READ commands for cart ROM

## Investigation Timeline

### Phase 1: Symptom Verification
- **Finding:** LCD is enabled (LCDC=$91) but display shows white screen
- **Conclusion:** Problem is NOT with VGA/LCD hardware, but with missing data

### Phase 2: Boot ROM Analysis
- **Test:** test_boot_rom_data.cpp
- **Finding:** Boot ROM loads correctly, all 256 bytes verified
- **Conclusion:** Boot ROM execution is correct

### Phase 3: Logo Copy Loop Analysis
- **Test:** test_boot_rom_flow.cpp
- **Finding:** Boot ROM reads from cart ROM $0104-$0133 (Nintendo logo)
- **Finding:** Logo copy writes only 5/96 bytes before aborting
- **Conclusion:** Cart ROM reads return zeros instead of logo data

### Phase 4: ioctl Download Interface Analysis
- **Test:** test_ioctl_interface.cpp
- **Finding:** ioctl writes accepted but CPU reads return all zeros
- **Root Cause #1 FOUND:** `dn_write` signal gated by `ce_cpu`

#### Bug #1: ce_cpu Gating (cart.v:372)

**Code Before (BUGGY):**
```verilog
if(speed?ce_cpu2x:ce_cpu) begin
    dn_write <= ioctl_wait_r;
    if(dn_write) {ioctl_wait_r, dn_write} <= 0;
end
```

**Code After (FIXED):**
```verilog
// CRITICAL FIX: Don't gate dn_write by ce_cpu
dn_write <= ioctl_wait_r;
if(dn_write) {ioctl_wait_r, dn_write} <= 0;
```

**Verification:** test_dn_write_pulse.cpp
- ✅ dn_write pulses on cycle 12 even with ce_cpu=0
- ✅ sdram_we pulses on cycle 12

### Phase 5: SDRAM Signal Path Analysis
- **Test:** test_sdram_addresses.cpp
- **Finding:** Write and read use same SDRAM address ($0082) ✓
- **Conclusion:** Address mapping is correct

### Phase 6: Boot ROM Shadowing Analysis
- **Test:** test_boot_rom_shadow.cpp
- **Finding:** All control signals correct during cart ROM reads:
  - `boot_rom_enabled = 1` (still active - correct for this stage)
  - `sel_boot_rom = 0` (not shadowing $0104 - correct!)
  - `cart_rd = 1` (cart read active - correct!)
  - `sdram_oe = 1` (SDRAM output enable - correct!)
- **Conclusion:** Signal path is correct, but data still returns $00

### Phase 7: SDRAM Memory Persistence Analysis
- **Test:** test_sdram_persistence.cpp
- **Critical Bug Found:** SDRAM model size was 0 bytes due to incorrect initialization
- **Fix:** Change `new MisterSDRAMModel(8*1024*1024)` to `new MisterSDRAMModel(8)`
- **Result:**
  - ✅ SDRAM write: Data persists! memory[0x104] = 0xCE, memory[0x105] = 0xED
  - ❌ CPU read: Still returns 0x00

### Phase 8: SDRAM Command Analysis
- **Test:** test_sdram_commands.cpp
- **Finding:** SDRAM write commands ARE issued:
  ```
  SDRAM: ACT bank=0 row=0
  SDRAM: WRITE bank=0 addr=0x000104 data=0xEDCE sel=0x00
  SDRAM: PRE bank=0 all=1
  ```
- **Critical Finding:** SDRAM statistics show:
  ```
  Writes: 1
  Reads: 0  ← NO READS HAPPENING!
  ```

## Current Status

### Fixed Issues ✅

1. **dn_write gating bug** (cart.v:372)
   - Removed ce_cpu gate from dn_write logic
   - Verified with test_dn_write_pulse.cpp
   - sdram_we now pulses correctly during ioctl downloads

2. **SDRAM write path**
   - Data written via ioctl persists in SDRAM memory
   - Verified with test_sdram_persistence.cpp
   - memory[0x104] = 0xCE, memory[0x105] = 0xED ✓

### Active Bug ❌

**SDRAM READ commands not being issued**

**Evidence:**
- `cart_rd = 1` ✓
- `sdram_oe = 1` ✓
- `sdram_addr = 0x0082` ✓
- But SDRAM model shows: Reads = 0

**Hypothesis:**
The SDRAM controller (rtl/sdram_sim.sv) is not translating the `oe` signal into actual READ commands. Possible causes:
1. Request latching issue (oe_pending not being set/processed)
2. State machine stuck in wrong state
3. Timing issue with sync signal
4. Missing transition from IDLE → ACTIVATE → READ

## Test Files Created

1. `test_boot_rom_data.cpp` - Verifies boot ROM loading ✅
2. `test_boot_rom_flow.cpp` - Traces logo copy execution ⚠️
3. `test_cart_rom_reads.cpp` - Monitors cart ROM reads ❌
4. `test_ioctl_interface.cpp` - Tests ioctl write/read ❌
5. `test_dn_write_pulse.cpp` - Verifies dn_write fix ✅
6. `test_ioctl_timing.cpp` - Diagnostic for ioctl timing
7. `test_boot_rom_shadow.cpp` - Checks boot ROM shadowing ✅
8. `test_sdram_addresses.cpp` - Verifies address mapping ✅
9. `test_sdram_commands.cpp` - Traces SDRAM commands
10. `test_sdram_persistence.cpp` - Verifies memory persistence ✅

## Next Steps

### Immediate Action Required

**Investigate SDRAM Controller READ Path**

File: `rtl/sdram_sim.sv`

**Questions to answer:**
1. Why isn't `oe` signal being latched into `oe_pending`?
2. Is the state machine transitioning correctly?
3. Is `sync` signal active when reads are attempted?
4. Are there additional conditions preventing READ commands?

**Debug approach:**
1. Add debug signals to expose sdram_sim.sv internal state:
   - `dbg_state` (already exists)
   - `dbg_oe_pending` (already exists)
   - `dbg_sync` (need to add)
   - `dbg_cycle` (need to add)

2. Create test to monitor controller state during cart ROM read

3. Compare working WRITE sequence vs broken READ sequence

### Long-term Fix Strategy

Once READ command issue is identified and fixed:

1. Verify cart ROM reads return correct data
2. Verify Nintendo logo copies to VRAM correctly (96 bytes)
3. Verify LCD displays logo animation
4. Test with multiple ROM files to ensure fix is comprehensive

## Technical Details

### Signal Paths

**Write Path:**
```
ioctl_wr → ioctl_wait_r → dn_write → sdram_we → SDRAM WRITE ✓
```

**Read Path:**
```
cart_rd → sdram_oe → ??? → SDRAM READ ✗ (broken here)
```

### SDRAM Address Mapping

**Write:** ioctl_addr[24:1] = $0104 >> 1 = $0082
**Read:** {1'b0, mbc_addr[22:1]} = {1'b0, $0104 >> 1} = $0082
**SDRAM:** bank=0, row=0, col=$82 → byte_addr = $0104 ✓

### Key Code Locations

- **cart.v:369-382** - dn_write logic (FIXED)
- **gameboy_sim.v:163-167** - SDRAM address/control assignment
- **rtl/sdram_sim.sv:149-162** - Request latching
- **rtl/sdram_sim.sv:176-189** - State machine transitions
- **rtl/sdram_sim.sv:163-196** - READ command generation

## Lessons Learned

1. **Clock enable gating:** Same bug pattern as boot ROM disable (gb.v:921) and LCDC register (video_sim.v:493). Critical control signals should NOT be gated by clock enables.

2. **Test parameter units:** MisterSDRAMModel constructor expects MB, not bytes. Wrong units caused memory.size() = 0.

3. **Separate write and read paths:** A bug in one doesn't imply a bug in the other - systematic verification of each path is essential.

4. **Signal path vs data path:** All control signals can be correct while the data path is broken - need to verify END-TO-END including actual data values.

## Conclusion

**Progress:** 2 of 3 bugs fixed (67% complete)

**Remaining work:** Fix SDRAM controller READ command generation

**Estimated impact:** High - this blocks ALL cart ROM functionality, not just boot sequence

**Priority:** CRITICAL - must be fixed for GameBoy emulation to work
