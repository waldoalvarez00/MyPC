# GameBoy Doctor Issues - Resolution Summary

## Overview

Successfully debugged and resolved two critical issues with the gameboy-doctor logger implementation:

1. **PCMEM showing all zeros** - Logger couldn't read instruction bytes
2. **PC not reaching expected address** - CPU execution started from wrong location

## Issues and Solutions

### Issue 1: PCMEM Shows All Zeros

**Problem:**
```
A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0914 PCMEM:00,00,00,00
A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0915 PCMEM:00,00,00,00
```

**Root Cause:**
- Boot ROM uploaded to **internal boot ROM memory** (not SDRAM)
- When `boot_rom_enabled=1`, CPU reads addresses 0x0000-0x00FF from internal ROM
- Logger's `read_pcmem()` only accessed SDRAM model
- SDRAM model has no visibility into internal boot ROM
- Result: Logger read zeros from SDRAM instead of actual boot ROM bytes

**Solution:**
Added boot ROM support to logger:
- Added `set_boot_rom()` method to store boot ROM copy
- Modified `read_pcmem()` to check boot ROM range first:
```cpp
if (addr < 0x0100 && dut->dbg_boot_rom_enabled && boot_rom_available) {
    // Read from boot ROM copy
    out[i] = boot_rom[addr];
} else if (addr < 0x8000) {
    // Read from SDRAM (cart ROM)
    out[i] = sdram->read_byte(addr);
}
```

**Result:**
```
PC:0002 PCMEM:01,00,00,00  ← Boot ROM bytes now visible!
PC:0150 PCMEM:11,04,01,1A  ← Cart ROM bytes visible!
```

### Issue 2: PC Not Reaching Expected Address

**Problem:**
- Test loaded program at 0x0150
- CPU execution started at PC=0x0165
- PC advanced to 0x01C8 range instead of running test code

**Root Cause:**
- Boot ROM upload used `run_cycles_with_sdram()` between writes
- CPU was NOT in reset during upload
- JP 0x0150 instruction executed during boot ROM upload process
- CPU jumped to 0x0150 but cart ROM not loaded yet
- CPU executed NOPs from unmapped memory (all zeros)
- By the time test program loaded at 0x0150, PC already past it

**Evidence:**
```
After reset, before boot ROM upload:
  PC = 0x0000

After boot ROM upload:
  PC = 0x015D    ← PC advanced during upload!
```

**Solution:**
Hold CPU in reset during ALL ROM uploads (following test_gui_raster_sanity.cpp pattern):

```cpp
// Step 1: Hold CPU in reset
dut->reset = 1;
run_cycles_with_sdram(dut, sdram, 200);

// Step 2: Upload boot ROM (CPU can't execute)
upload_boot_rom(dut, sdram);

// Step 3: Load cart ROM to SDRAM
load_cart_rom_to_sdram(sdram);

// Step 4: Initialize cart
init_cart_ready(dut, sdram);

// Step 5: Release reset (CPU starts at PC=0x0000)
run_cycles_with_sdram(dut, sdram, 500);
dut->reset = 0;
```

**Result:**
- CPU stays at PC=0x0000 during ROM uploads
- When reset released, CPU starts from 0x0000 with complete ROMs loaded
- CPU correctly executes: 0x0000 (boot ROM) → 0x0100 (cart header) → 0x0150 (test code)

## Files Modified

### 1. gb_doctor_logger.h
**Changes:**
- Added `uint8_t boot_rom[256]` member
- Added `bool boot_rom_available` flag
- Added `set_boot_rom()` method
- Modified `read_pcmem()` to check boot ROM first

**Lines modified:** ~10 additions

### 2. test_doctor_inc_de.cpp
**Created new test demonstrating both fixes:**
- Holds CPU in reset during ROM upload
- Provides boot ROM copy to logger
- Verifies PCMEM shows actual bytes
- Verifies PC reaches expected addresses

## Test Results

### Before Fixes

**test_doctor_simple.cpp output:**
```
Instructions logged: 78
Final PC: 0x0961
PCMEM: All zeros
Status: FAIL - wrong PC range, no instruction data
```

### After Fixes

**test_doctor_inc_de.cpp output:**
```
Instructions logged: 10
Final PC: 0x0157 (expected 0x0157) ✓
Final DE: 0x0105 (expected 0x0105) ✓
Final A:  0xED (expected 0xED) ✓
Status: PASS
```

**Log file (logs/inc_de_doctor.log):**
```
A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0002 PCMEM:01,00,00,00
A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0150 PCMEM:11,04,01,1A
A:00 F:00 B:00 C:00 D:00 E:04 H:00 L:00 SP:FFFE PC:0153 PCMEM:1A,13,1A,76
A:CE F:00 B:00 C:00 D:01 E:04 H:00 L:00 SP:FFFE PC:0154 PCMEM:13,1A,76,00
A:CE F:00 B:00 C:00 D:01 E:05 H:00 L:00 SP:FFFE PC:0155 PCMEM:1A,76,00,00
A:ED F:00 B:00 C:00 D:01 E:05 H:00 L:00 SP:FFFE PC:0157 PCMEM:00,00,00,00
```

**Analysis:**
- ✅ PCMEM shows actual instruction bytes (11, 04, 01, 1A, 13, 76, etc.)
- ✅ PC sequence correct: 0x0002 → 0x0150 → 0x0153 → 0x0154 → 0x0155 → 0x0157
- ✅ Register values correct (DE=0x0105, A=0xED)
- ✅ Boot ROM bytes visible (PC:0002 PCMEM:01,00,00,00)

## Key Learnings

### Memory Architecture
1. **Boot ROM is internal** - Not stored in SDRAM model
2. **Memory read priority:**
   - If `boot_rom_enabled=1` AND `addr < 0x0100`: Read internal boot ROM
   - Otherwise: Read from SDRAM (cart ROM)
3. **Logger needs both sources** - SDRAM for cart ROM, boot ROM copy for boot ROM bytes

### ROM Loading Sequence
1. **Always hold reset** during ROM uploads
2. **Load order:**
   - Hold reset
   - Upload boot ROM
   - Load cart ROM to SDRAM
   - Initialize cart
   - Release reset
3. **Never run cycles** while loading unless CPU in reset

### Reference Implementation
**test_gui_raster_sanity.cpp (lines 103-126):**
```cpp
// Hold the core in reset while we inject the boot ROM and initialize cart state.
// If reset is released too early, the CPU can start executing with an empty boot ROM
// and before cart_ready is asserted, leading to permanent 0x00 reads from ROM.
dut->reset = 1;
...
download_boot_rom(dut, sdram, boot.data(), boot.size());
init_cart_without_writes(dut, sdram);
wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 5000, sdram);
run_cycles_with_sdram(dut, sdram, 500);
dut->reset = 0;
```

## Testing Checklist

For any new gameboy-doctor test:

- [ ] Hold CPU in reset during ROM load
- [ ] Upload boot ROM while reset=1
- [ ] Load cart ROM to SDRAM while reset=1
- [ ] Initialize cart while reset=1
- [ ] Wait for cart_ready
- [ ] Release reset
- [ ] Create logger with `set_boot_rom()` if logging boot ROM
- [ ] Verify PCMEM shows actual bytes (not zeros)
- [ ] Verify PC reaches expected addresses

## Documentation Created

1. **MCYCLE_DEBUG_RESULTS.md** - M-cycle detection fix (PC-based instead of M-cycle transitions)
2. **GAMEBOY_DOCTOR_SETUP_COMPLETE.md** - Full infrastructure setup guide
3. **PCMEM_AND_PC_ISSUES_RESOLVED.md** - Detailed analysis of both issues
4. **ISSUES_RESOLVED_SUMMARY.md** - This document

## Next Steps

The gameboy-doctor infrastructure is now complete and functional:

1. **Logger works correctly** - Captures CPU state with real instruction bytes
2. **Test framework ready** - Can create tests following test_doctor_inc_de.cpp pattern
3. **Ready for real testing:**
   - Can use actual DMG boot ROM (dmg_boot.bin)
   - Can load real game ROMs
   - Can compare against SameBoy reference traces
   - Can pinpoint exact instruction where divergence occurs

## Example Usage

```cpp
// Create test
Vtop* dut = new Vtop();
MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);

// Hold reset and load ROMs
dut->reset = 1;
upload_boot_rom(dut, sdram, boot_data, 256);
load_cart_to_sdram(sdram, cart_data, cart_size);
init_cart_ready(dut, sdram);

// Release reset
dut->reset = 0;

// Create logger
GBDoctorLogger logger("output.log");
logger.set_boot_rom(boot_data, 256);
logger.set_enabled(true);

// Run and log
for (int cycle = 0; cycle < max_cycles; cycle++) {
    tick_with_sdram(dut, sdram);
    logger.tick(dut, sdram);
}

// Log will contain correct PCMEM data and proper PC progression!
```

## Conclusion

Both critical issues resolved:
- ✅ PCMEM now shows actual instruction bytes
- ✅ PC correctly reaches expected addresses
- ✅ Logger infrastructure complete and tested
- ✅ Ready for gameboy-doctor comparative debugging

The gameboy-doctor tool is now operational and ready to help locate bugs in the GameBoy RTL implementation by comparing execution traces against known-good reference implementations.
