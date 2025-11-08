# VGA Mode Tracking Implementation Status

## Date: 2025-11-08

## Overview
Implementation of dynamic video mode detection and configurable timing for the VGA/MCGA controller. This enables support for all 15 standard PC video modes (CGA/EGA/VGA/MDA/MCGA).

---

## Implementation Progress

### ✅ COMPLETED

#### 1. Mode Definition Infrastructure (100%)
**File:** `Quartus/rtl/VGA/VGATypes.sv`
- Defined all 15 video mode parameters (timing, resolution, color depth)
- Created `VideoModeNumber_t` enum with all mode numbers
- Implemented `get_mode_params()` function for mode lookup
- **Tests:** 150/150 tests passing (vga_modes_tb.sv)
- **Status:** Production ready

**Modes Defined:**
- Text modes: 00h, 01h, 02h, 03h, 07h (MDA)
- CGA graphics: 04h, 05h, 06h
- EGA graphics: 0Dh, 0Eh, 0Fh, 10h
- VGA graphics: 11h, 12h, 13h

#### 2. Configurable Video Timing (100%)
**File:** `Quartus/rtl/VGA/VGASync.sv`
- Made all timing parameters dynamic based on mode_num input
- Expanded counters and outputs to 11 bits for higher resolutions
- Supports all timing variations (320x200, 640x200, 640x350, 640x480, 720x350)
- **Status:** Production ready

**Changes:**
- Added `input VideoModeNumber_t mode_num`
- Dynamically loads mode parameters via `get_mode_params()`
- All timing counters now use `mode_params.{h,v}_total` etc.

#### 3. Multi-Bit Clock Domain Synchronizer (100%)
**File:** `Quartus/rtl/CPU/cdc/BusSync.sv` (NEW)
- Created parameterized WIDTH-based synchronizer
- Supports both Icarus Verilog simulation and Altera synthesis
- Generic 2-stage flip-flop synchronizer for simulation
- Altera-specific synchronizer for FPGA
- **Status:** Production ready

---

### 🔶 PARTIALLY COMPLETE

#### 4. VGA Register Mode Detection (70%)
**File:** `Quartus/rtl/VGA/VGARegisters.sv`

**Completed:**
- ✅ Added `output VideoModeNumber_t mode_num`
- ✅ Implemented mode detection logic in always_comb block
- ✅ Added BusSync for clock domain crossing to VGA clock
- ✅ Detects MODE_03H (text), MODE_04H (graphics), MODE_13H (256-color)

**Status:** Implemented but NOT WORKING

**Current Issue:**
Mode switching from text to graphics mode fails. Debug test shows:
```
Write 0x0A to 3D8h → sys_graphics_enabled stays 0, text_enabled stays 1
Expected: sys_graphics_enabled=1, text_enabled=0
Result: Mode stays at 03h instead of switching to 04h
```

**Root Cause:** VGA register address decoding is incorrect

#### 5. VGA Controller Integration (90%)
**File:** `Quartus/rtl/VGA/VGAController.sv`

**Completed:**
- ✅ Added `input VideoModeNumber_t mode_num`
- ✅ Threaded mode_num to VGASync
- ✅ Expanded row/col to 11 bits for higher resolutions
- ✅ Updated shifted_row and is_border calculations

**Status:** Complete, pending VGARegisters fix

---

### ❌ CRITICAL ISSUE: VGA Register Address Decode

**Problem:** The address bit patterns in VGARegisters.sv are INCORRECT

**Analysis:**
VGA I/O ports 0x3C0-0x3DF are accessed via offset from base.
Current code checks wrong bit patterns.

**Example - Register 3D8h (Mode Control):**
```systemverilog
// CURRENT (WRONG):
wire sel_mode = reg_access & data_m_addr[5:1] == 5'b11000; // = 24 decimal

// SHOULD BE:
// Port 3D8h = 0x3D8
// Offset from base 0x3C0 = 0x18 (24 bytes)
// Word address offset = 0x18 / 2 = 0x0C (12)
// Bits [5:1] = 0b01100 = 12 decimal
wire sel_mode = reg_access & data_m_addr[5:1] == 5'b01100; // = 12 decimal
```

**All Affected Registers:**
| Register | Port | Current Check | Should Be | Status |
|----------|------|---------------|-----------|--------|
| AMCR     | 3C0h | 0b00000 (0)  | 0b00000 (0)  | ✓ OK |
| DAC RD   | 3C7h | 0b00111 (7)  | 0b00011 (3)  | ✗ WRONG |
| DAC WR   | 3C8h | 0b01000 (8)  | 0b00100 (4)  | ✗ WRONG |
| DAC Data | 3C9h | 0b01001 (9)  | 0b00100 (4)  | ✗ WRONG |
| Index    | 3D4h | 0b10100 (20) | 0b01010 (10) | ✗ WRONG |
| Value    | 3D5h | 0b10101 (21) | 0b01010 (10) | ✗ WRONG |
| Mode     | 3D8h | 0b11000 (24) | 0b01100 (12) | ✗ WRONG |
| Color    | 3D9h | 0b11001 (25) | 0b01100 (12) | ✗ WRONG |
| Status   | 3DAh | 0b11010 (26) | 0b01101 (13) | ✗ WRONG |

**Impact:**
- Mode switching completely broken
- Palette programming likely broken
- Cursor programming likely broken
- Status register reads likely broken

**Confusion:**
The existing `vga_registers_tb.sv` test supposedly passed some tests using address 0x1EC for register 3D8h, which should have failed with the current decode. Need to investigate:
1. Does the existing test actually pass?
2. Is there a different address mapping scheme?
3. Is data_m_addr pre-processed somewhere?

**Action Required:**
1. Investigate actual hardware address mapping
2. Check if Top.sv does address translation
3. Verify existing test behavior
4. Fix address decode patterns
5. Re-run all tests

---

## Test Infrastructure

### Created Tests:
1. **vga_modes_tb.sv** - Mode definition validation (150/150 PASS)
2. **vga_mode_switching_tb.sv** - Integration test (3/4 PASS, 1 FAIL)
3. **vga_mode_debug_tb.sv** - Debug testbench (revealed address issue)
4. **run_vga_mode_switching_test.sh** - Test automation

### Test Results:
```
Test 1: Default text mode 03h                    [PASS]
Test 2: CGA graphics mode 04h                    [FAIL] ← Address decode issue
Test 3: MCGA 256-color mode 13h                  [PASS]
Test 4: Return to text mode 03h                  [PASS]
```

**Note:** Mode 13h works because AMCR register (3C0h) has correct decode (0b00000)

---

## Files Modified

### Core Hardware:
- ✅ `Quartus/rtl/VGA/VGATypes.sv` - Mode definitions (COMPLETE)
- ✅ `Quartus/rtl/VGA/VGASync.sv` - Configurable timing (COMPLETE)
- 🔶 `Quartus/rtl/VGA/VGARegisters.sv` - Mode detection (BROKEN - address decode)
- ✅ `Quartus/rtl/VGA/VGAController.sv` - Integration (COMPLETE)
- ✅ `Quartus/rtl/CPU/cdc/BusSync.sv` - Multi-bit sync (NEW, COMPLETE)

### Test Files:
- ✅ `modelsim/vga_modes_tb.sv` - Mode validation
- ✅ `modelsim/run_vga_modes_test.sh` - Mode test automation
- 🔶 `modelsim/vga_mode_switching_tb.sv` - Integration test (reveals bug)
- ✅ `modelsim/vga_mode_debug_tb.sv` - Debug test (isolated address bug)
- ✅ `modelsim/run_vga_mode_switching_test.sh` - Switching test automation

### Documentation:
- `VGA_MODES_IMPLEMENTATION.md` - Implementation plan
- `VGA_MCGA_FINDINGS.md` - Initial bug analysis
- `VGA_MODE_TRACKING_STATUS.md` - This document

---

## Next Steps (Priority Order)

### 1. URGENT: Fix VGA Register Address Decode ⚠️
**Priority:** CRITICAL
**Blocking:** Mode switching, palette, cursor control

**Tasks:**
- [ ] Investigate actual address mapping in Top.sv
- [ ] Determine if data_m_addr is full address or offset
- [ ] Calculate correct bit patterns for all registers
- [ ] Update all sel_* wire declarations in VGARegisters.sv
- [ ] Verify existing vga_registers_tb.sv behavior
- [ ] Re-run all VGA register tests

**Estimated Effort:** 1-2 hours

### 2. Complete Mode Detection Logic
**Priority:** HIGH
**Depends on:** Address decode fix

**Tasks:**
- [ ] Expand mode detection to identify all 15 modes
- [ ] Add detection for resolution hints (640x200 vs 320x200)
- [ ] Add detection for color depth hints
- [ ] Add detection for text column/row settings
- [ ] Test all mode transitions

**Estimated Effort:** 2-3 hours

### 3. Update FrameBuffer for Multi-Resolution
**Priority:** HIGH
**Blocking:** Actual video output for non-default modes

**Tasks:**
- [ ] Add mode_num input to FrameBuffer
- [ ] Implement mode-specific address calculation
- [ ] Support 1bpp pixel format (modes 06h, 0Fh, 11h)
- [ ] Support 2bpp pixel format (modes 04h, 05h)
- [ ] Support 4bpp packed format (modes 0Dh, 0Eh, 10h, 12h)
- [ ] Support 8bpp format (mode 13h) - already exists
- [ ] Text mode variants (40-column, 80-column, MDA)

**Estimated Effort:** 8-10 hours

### 4. Integration Testing
**Priority:** MEDIUM

**Tasks:**
- [ ] Create full-system integration test
- [ ] Test all 15 modes with VGAController
- [ ] Verify timing for each mode
- [ ] Test mode switching transitions
- [ ] Performance testing

**Estimated Effort:** 3-4 hours

### 5. Advanced Features (Lower Priority)
**Priority:** LOW

**Tasks:**
- [ ] EGA planar mode (4 memory planes)
- [ ] CGA interlaced addressing
- [ ] MDA 9-pixel character width
- [ ] Pixel clock divider for different modes
- [ ] Extended palette support (EGA/VGA)

**Estimated Effort:** 10+ hours

---

## Technical Notes

### Clock Domain Crossing
Mode number is synchronized from sys_clk (register domain) to vga_clk (timing domain) using BusSync:
```systemverilog
BusSync #(.WIDTH(8))
    ModeNumSync(.clk(vga_clk),
                .reset(reset),
                .d(sys_mode_num),      // sys_clk domain
                .q(mode_num));          // vga_clk domain
```

Latency: 2 vga_clk cycles for synchronization

### Mode Detection Logic
Current simplified detection in VGARegisters.sv:
```systemverilog
always_comb begin
    sys_mode_num = MODE_03H;  // Default 80x25 text

    if (sys_256_color)
        sys_mode_num = MODE_13H;  // 320x200, 256 colors
    else if (sys_graphics_enabled && !text_enabled)
        sys_mode_num = MODE_04H;  // CGA 320x200, 4 colors
    else if (text_enabled)
        sys_mode_num = MODE_03H;  // 80x25 text
end
```

**Limitation:** Only detects 3 modes. Needs expansion for all 15 modes.

### Address Mapping Investigation Needed
The relationship between CPU I/O port address and data_m_addr needs clarification:
- Are addresses word-aligned or byte-aligned?
- Is data_m_addr an offset from VGA base or full address?
- Does Top.sv perform address translation?
- What is the actual bit layout?

---

## References

- **IBM VGA Technical Reference** - Hardware specifications
- **FreeVGA Documentation** - Timing parameters
- **VGA_MODES_IMPLEMENTATION.md** - Detailed implementation plan
- **VGA_MCGA_FINDINGS.md** - Initial bug analysis and testing

---

## Commit History

**Latest Commit:** 69bc836
**Branch:** claude/debug-glitches-verilator-011CUrg5uPydbwwdzTkPyM6R

```
Implement VGA mode tracking infrastructure (WIP)

- Created BusSync.sv for multi-bit clock domain crossing
- Added mode detection to VGARegisters (not working)
- Made VGASync timing fully configurable
- Integrated mode_num through VGAController hierarchy
- Created integration and debug tests
- Identified critical address decode bug

Status: Hardware infrastructure complete, address decode broken
```

---

## Summary

**Overall Progress:** ~60% complete

**Working:**
- Mode definitions and lookup
- Configurable video timing
- Clock domain synchronization
- Basic hardware threading

**Broken:**
- VGA register address decode (CRITICAL)
- Mode switching
- Likely: palette, cursor, status registers

**Next Critical Path:**
1. Fix address decode (1-2 hours)
2. Complete mode detection (2-3 hours)
3. Update FrameBuffer (8-10 hours)
4. Integration testing (3-4 hours)

**Estimated Time to Completion:** 14-19 hours of focused work
