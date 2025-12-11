# GameBoy Simulator - Boot ROM Execution Analysis

## Summary

The interrupt storm issue at PC=0x0038 is **NOT caused by interrupts at all**. The root cause is that **PC execution goes wild into high memory** (0xFFFD) after boot ROM disables itself, and then jumps to 0x0038.

## Diagnostic Results

### Test 1: diagnose_pc_stuck.cpp
- **Result**: PC stuck at 0x0038 after cycle 3470
- **boot_rom_enabled**: 1 (BOOT ROM STILL ENABLED!)
- **Conclusion**: Real DMG boot ROM gets stuck and never completes

### Test 2: test_minimal_boot_rom.cpp (with LCD initialization)
- **Result**: PC stuck at 0x0038 after cycle 2968
- **boot_rom_enabled**: 0 (Boot ROM disabled)
- **Conclusion**: Boot ROM completes, but cart ROM has interrupt storm

### Test 3: test_simple_boot_rom.cpp (NO LCD initialization)
- **Result**: PC stuck at 0x0038 after cycle 2648
- **boot_rom_enabled**: 0 (Boot ROM disabled)
- **Conclusion**: Even with LCD OFF, interrupt storm still occurs

### Test 4: diagnose_0x0038_issue.cpp (detailed PC tracking)
- **Result**: PC at 0xFFFD (high memory) before jumping to 0x0038
- **Previous PC**: 0xFFFD (stuck there for many cycles)
- **SP**: 0xFFFD (same as PC!)
- **Instruction at 0xFFFD**: 0x00 (NOP - but this is not code area!)
- **Conclusion**: PC execution goes into register space (0xFFFD-0xFFFF), NOT valid code

## Root Cause

The boot ROM's `JP $0100` instruction (jump to cart entry point) is **NOT working correctly**. Instead of jumping to 0x0100, execution continues into high memory at 0xFFFD (near the IE register at 0xFFFF).

Possible causes:
1. **JP instruction encoding error** - The boot ROM might have incorrect bytes for the JP instruction
2. **Boot ROM upload issue** - The boot ROM might not be uploaded correctly to the simulator
3. **Boot ROM disable timing** - The boot ROM might be disabling itself while JP is executing
4. **SDRAM timing issue** - With realistic CAS latency=2, the boot ROM read timing might be broken

## Evidence

### Boot ROM Code (from test):
```cpp
minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;  // LD A, $01
minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;  // LDH ($FF50), A  ; Disable boot ROM
minimal_boot[pc++] = 0xC3; minimal_boot[pc++] = 0x00; minimal_boot[pc++] = 0x01;  // JP $0100
```

The JP instruction is encoded as: `0xC3 0x00 0x01` (JP $0100)

### Execution Trace:
1. Boot ROM executes (cycles 0-400)
2. Boot ROM writes to $FF50 to disable itself (cycle ~400)
3. **JP $0100 instruction should execute**
4. **Instead, PC goes to 0xFFFD** (cycle ~400)
5. PC stuck at 0xFFFD (cycles 400-413)
6. PC jumps to 0x0038 (cycle 414)

## Hypothesis: Boot ROM Disable Timing Race Condition

The issue might be a **race condition** between:
1. Writing to $FF50 (boot ROM disable register)
2. Executing JP $0100 instruction

If the boot ROM disables itself BEFORE the JP instruction completes fetching its operand bytes, the CPU might:
1. Fetch opcode 0xC3 (JP) from boot ROM
2. Boot ROM disables (boot_rom_enabled = 0)
3. Fetch operand bytes (0x00 0x01) from CART ROM instead of boot ROM
4. Cart ROM at addresses right after boot ROM might contain 0xFF (uninitialized)
5. JP decodes to wrong address → PC goes wild

## Solution Attempts

### ❌ Attempt 1: Force minimal boot ROM instead of real DMG
**File**: sim_main_gui.cpp line 1106
**Change**: Commented out `loadBootROM()` call
**Result**: Still fails - boot ROM completes but PC goes to 0xFFFD

### ❌ Attempt 2: Keep LCD OFF to prevent interrupts
**Test**: test_simple_boot_rom.cpp
**Result**: Still fails - not an interrupt issue

### ❌ Attempt 3: Clear IE register to prevent all interrupts
**Test**: test_simple_boot_rom.cpp
**Result**: Still fails - not an interrupt issue

## Real Solution Required

The real fix needs to address the boot ROM → cart ROM transition:

### Option 1: Fix JP $0100 Timing
Ensure that when boot ROM executes `JP $0100`, all 3 bytes (0xC3 0x00 0x01) are fetched from the boot ROM BEFORE it disables itself.

### Option 2: Different Boot ROM Disable Method
Instead of writing to $FF50 and then JP, do:
```assembly
LD HL, $0100    ; Load target address
LD A, $01       ; Prepare boot ROM disable value
LDH ($FF50), A  ; Disable boot ROM
JP (HL)         ; Jump via register (might be more reliable)
```

### Option 3: Add Delay After Boot ROM Disable
```assembly
LDH ($FF50), A  ; Disable boot ROM
NOP             ; Wait 1 cycle
NOP             ; Wait 1 cycle
JP $0100        ; Now jump (cart ROM stable)
```

### Option 4: Use Real DMG Boot ROM Properly
The real DMG boot ROM likely has proper timing for this transition. The issue with the real boot ROM getting stuck at 0x0038 (in Test 1) suggests:
- Real DMG boot ROM has its OWN issue with realistic SDRAM latency
- Real DMG boot ROM might need zero-latency SDRAM to work
- We need to debug why real DMG boot ROM fails first

## Files Affected

1. **sim_main_gui.cpp** (line 1106) - Boot ROM loading disabled
2. **diagnose_pc_stuck.cpp** - Created diagnostic tool
3. **test_minimal_boot_rom.cpp** - Created test with minimal boot ROM
4. **test_simple_boot_rom.cpp** - Created test with LCD OFF
5. **diagnose_0x0038_issue.cpp** - Created detailed PC tracking diagnostic

## Next Steps

1. **Investigate boot ROM upload** - Verify that boot ROM bytes are correctly uploaded to simulator
2. **Check boot ROM memory mapping** - Verify that boot ROM is mapped at 0x0000-0x00FF
3. **Test with zero-latency SDRAM** - See if real DMG boot ROM works with cas_latency=0
4. **Add boot ROM execution trace** - Log each instruction executed by boot ROM to see where it diverges

## Status

❌ **ISSUE NOT RESOLVED**

The interrupt storm fix in sim_main_gui.cpp (disabling real DMG boot ROM) does NOT solve the problem. The root cause is a boot ROM → cart ROM transition issue, NOT an interrupt issue.

---

*Analysis Date: 2025-12-11*
*Diagnostics: 4 tests created*
*Root Cause: PC goes to high memory (0xFFFD) after boot ROM disables*
*Issue Type: Boot ROM transition timing / memory mapping*
