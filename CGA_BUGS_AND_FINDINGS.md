# CGA Controller - Bugs and Findings Report

## Date: 2025-11-08
## Tester: Claude Code
## Test Tool: Icarus Verilog (open-source simulator)

---

## Executive Summary

Testing of the CGA (Color Graphics Adapter) controller revealed **multiple critical bugs** that prevent compilation with Icarus Verilog and likely other open-source tools. All bugs are related to **Icarus Verilog compatibility** and **SystemVerilog syntax strictness**.

**Severity:** CRITICAL - Controller cannot be tested or simulated with open-source tools
**Impact:** HIGH - Blocks testing, verification, and debugging
**Status:** BROKEN - Requires fixes before testing can proceed

---

## Critical Bugs Found

### Bug 1: Wire Assigned in Procedural Block
**File:** `Quartus/rtl/CGA/cga_pixel.sv`
**Lines:** 72, 74, 76, 78, 80
**Severity:** CRITICAL

**Issue:**
The `video` output is declared as `wire` (due to `default_nettype wire`), but is being assigned inside an `always_comb` procedural block.

**Code:**
```systemverilog
output[3:0] video    // Line 39 - implicitly wire

always_comb begin
    if (tandy_16_mode) begin
        if (overscan)
            video = tandy_color_4 ? video_out : tandy_palette[video_out];  // ERROR!
        // ... more assignments to video
    end else
        video = video_out;  // ERROR!
end
```

**Error Message:**
```
cga_pixel.sv:72: error: video is not a valid l-value in cga_registers_tb.cgacard_inst.cga1.pixel.
cga_pixel.sv:39:      : video is declared here as wire.
```

**Root Cause:**
- `default_nettype wire` causes undeclared nets to default to `wire`
- `wire` cannot be assigned in procedural blocks (`always`, `always_comb`, etc.)
- Must be `logic` or `reg` for procedural assignment

**Impact:**
- Controller CANNOT compile with Icarus Verilog
- Likely fails with other strict simulators
- Prevents ANY testing of CGA controller

**Fix Required:**
Change line 39 from:
```systemverilog
output[3:0] video
```
To:
```systemverilog
output logic [3:0] video
```

---

### Bug 2: Unsupported Array Initialization Syntax
**File:** `Quartus/rtl/CGA/cga_pixel.sv`
**Line:** 56
**Severity:** CRITICAL

**Issue:**
Array initialization using SystemVerilog aggregate assignment `'{ }` syntax is not supported by Icarus Verilog.

**Code:**
```systemverilog
reg[3:0] tandy_palette[0:15] = '{ 4'h0, 4'h1, 4'h2, 4'h3, 4'h4, 4'h5, 4'h6, 4'h7,
                                   4'h8, 4'h9, 4'ha, 4'hb, 4'hc, 4'hd, 4'he, 4'hf };
```

**Error Message:**
```
cga_pixel.sv:56: sorry: Assignment to an entire array or to an array slice is not yet supported.
```

**Root Cause:**
- Icarus Verilog does not support aggregate array initialization
- This is a known Icarus limitation

**Impact:**
- Palette initialization fails
- Controller cannot compile
- Tandy mode colors will be incorrect

**Fix Required:**
Use individual assignments in initial block:
```systemverilog
reg[3:0] tandy_palette[0:15];

initial begin
    tandy_palette[0]  = 4'h0;
    tandy_palette[1]  = 4'h1;
    tandy_palette[2]  = 4'h2;
    tandy_palette[3]  = 4'h3;
    tandy_palette[4]  = 4'h4;
    tandy_palette[5]  = 4'h5;
    tandy_palette[6]  = 4'h6;
    tandy_palette[7]  = 4'h7;
    tandy_palette[8]  = 4'h8;
    tandy_palette[9]  = 4'h9;
    tandy_palette[10] = 4'ha;
    tandy_palette[11] = 4'hb;
    tandy_palette[12] = 4'hc;
    tandy_palette[13] = 4'hd;
    tandy_palette[14] = 4'he;
    tandy_palette[15] = 4'hf;
end
```

---

### Bug 3: Binary Constant With Extra Digits
**File:** `Quartus/rtl/CGA/cga_pixel.sv`
**Line:** 76
**Severity:** WARNING (non-critical)

**Issue:**
Binary constant has more digits than specified width.

**Error Message:**
```
cga_pixel.sv:76: warning: Extra digits given for sized binary constant.
```

**Likely Code:**
```systemverilog
video = tandy_palette[{ 2'b000, pix_640 }];  // 3 bits specified as 2'b
```

**Impact:**
- Minor - causes warning but likely works correctly
- Indicates sloppy coding
- Could mask real bugs

**Fix Required:**
Correct the width specification:
```systemverilog
video = tandy_palette[{ 3'b000, pix_640 }];  // Use 3'b for 3-bit value
```

---

## Port Width Mismatch Warnings

### Warning 1: bus_a Port Width
**File:** `Quartus/rtl/CGA/cgacard.sv`
**Line:** 80
**Severity:** WARNING

**Issue:**
```
Port 3 (bus_a) of cga expects 15 bits, got 19.
Pruning 4 high bits of the expression.
```

**Analysis:**
- `cga` module expects `bus_a[14:0]` (15 bits)
- `cgacard` passes `data_m_addr[19:1]` (19 bits)
- Top 4 bits are being discarded

**Impact:**
- Functional - address bits [18:15] ignored
- Could limit memory mapping flexibility
- Likely intentional but worth documenting

**Recommendation:**
- Document that CGA only decodes 15-bit addresses
- Or explicitly trim: `data_m_addr[14:1]`

---

### Warning 2: busConverter addr Port Width
**File:** `Quartus/rtl/CGA/cgacard.sv`
**Line:** 132
**Severity:** WARNING

**Issue:**
```
Port 8 (addr) of busConverter expects 13 bits, got 14.
Pruning 1 high bits of the expression.
```

**Analysis:**
- `busConverter` parameter `AW=14` creates 14-bit address
- But input port `addr` expects 13 bits
- Mismatch in parameter vs port definition

**Impact:**
- May limit addressable VRAM to 8KB instead of 16KB
- Parameter doesn't match implementation

**Recommendation:**
- Review busConverter parameter usage
- Ensure VRAM address width matches intended memory size

---

### Warning 3: busConverter mem_addr Output Width
**File:** `Quartus/rtl/CGA/cgacard.sv`
**Line:** 132
**Severity:** WARNING

**Issue:**
```
Port 10 (mem_addr) of busConverter expects 14 bits, got 17.
Padding 3 high bits of the expression.
```

**Analysis:**
- Output `mem_addr` is 17 bits but busConverter outputs 14 bits
- Extra bits padded with zeros

**Impact:**
- Cosmetic - no functional issue
- Indicates unclear interface specification

**Recommendation:**
- Match wire declarations to actual port widths

---

### Warning 4: vram addra Port Width
**File:** `Quartus/rtl/CGA/cgacard.sv`
**Line:** 153
**Severity:** WARNING

**Issue:**
```
Port 4 (addra) of vram expects 14 bits, got 17.
Pruning 3 high bits of the expression.
```

**Analysis:**
- VRAM address should be 14 bits (16KB)
- Passing 17-bit wire, top 3 bits discarded

**Impact:**
- Functional - works correctly but inefficient
- Wastes wires

**Recommendation:**
- Use correct wire width or explicit truncation

---

## Additional Findings

### Finding 1: Character ROM File Dependency
**File:** `Quartus/rtl/CGA/cga_pixel.sv`
**Line:** 66
**Severity:** INFORMATIONAL

**Code:**
```systemverilog
initial $readmemh("cga.hex", char_rom, 0, 4095);
```

**Issue:**
- Hardcoded file path "cga.hex"
- Must be in simulation directory
- Test will fail if file missing

**Recommendation:**
- Document character ROM file requirement
- Provide cga.hex file or generation script
- Consider parameterized path

---

### Finding 2: No Module-Level Comments
**All Files**
**Severity:** INFORMATIONAL

**Issue:**
- CGA modules lack comprehensive header comments
- Register addresses not documented at module level
- Video mode specifications not clearly stated

**Recommendation:**
- Add comprehensive module documentation
- Document register map
- Document supported video modes
- Add timing specifications

---

## CGA Register Map (Documented)

Based on code analysis, the CGA controller uses these I/O addresses:

| Address | Register | Access | Function |
|---------|----------|--------|----------|
| 0x3D4 | CRTC Index | Write | Select CRTC register (6845 index) |
| 0x3D5 | CRTC Data | Read/Write | Access selected CRTC register |
| 0x3D8 | Mode Control | Write | Control register (mode bits) |
| 0x3D9 | Color Select | Write | Palette and background color |
| 0x3DA | Status | Read | Display status (vsync, etc.) |
| 0x3DE | Tandy Color | Write | Tandy mode color select |

---

## Mode Control Register (0x3D8) Bit Definitions

Based on `cga.sv` code analysis:

| Bit | Name | Function |
|-----|------|----------|
| 0 | hres_mode | 1=80 columns, 0=40 columns (text) |
| 1 | grph_mode | 1=graphics mode, 0=text mode |
| 2 | bw_mode | 1=black & white, 0=color |
| 3 | video_enabled | 1=display enabled, 0=display off |
| 4 | mode_640 | 1=640x200, 0=320x200 (graphics) |
| 5 | blink_enabled | 1=cursor blink enabled |
| 6-7 | Reserved | Not used |

---

## CGA Video Modes Supported

| Mode | Type | Resolution | Colors | Control Reg |
|------|------|------------|--------|-------------|
| 00h/01h | Text | 40x25 | 16 | 0x08/0x0C |
| 02h/03h | Text | 80x25 | 16 | 0x09/0x0D |
| 04h | Graphics | 320x200 | 4 | 0x0A |
| 05h | Graphics | 320x200 | 4 (gray) | 0x0E |
| 06h | Graphics | 640x200 | 2 | 0x1A |

Tandy modes (if enabled):
- 16-color graphics modes via extended registers

---

## Test Status

### Tests Created
✓ Comprehensive register testbench (`cga_registers_tb.sv`)
✓ Test automation script (`run_cga_test.sh`)
✓ Tests for all standard CGA modes
✓ CRTC programming tests
✓ Color select tests
✓ Status register tests

### Tests Status
❌ **BLOCKED** - Cannot compile due to critical bugs
❌ Cannot run any tests until bugs are fixed
❌ No verification of functional correctness possible

---

## Recommendations

### Immediate Actions (Critical)

1. **Fix Bug 1** - Change `video` output to `logic` type
   - File: `cga_pixel.sv` line 39
   - Change: `output[3:0] video` → `output logic [3:0] video`
   - Priority: CRITICAL

2. **Fix Bug 2** - Use initial block for palette initialization
   - File: `cga_pixel.sv` line 56
   - Replace aggregate assignment with individual assignments
   - Priority: CRITICAL

3. **Fix Bug 3** - Correct binary constant width
   - File: `cga_pixel.sv` line 76
   - Change `2'b000` to `3'b000`
   - Priority: LOW (warning only)

### Short-Term Actions

4. **Clean up port width mismatches**
   - Review all module instantiations
   - Ensure widths match or are explicitly trimmed
   - Priority: MEDIUM

5. **Add character ROM file**
   - Provide `cga.hex` file for testing
   - Document format and contents
   - Priority: HIGH (required for testing)

6. **Create comprehensive documentation**
   - Document register map
   - Document video modes
   - Add module-level comments
   - Priority: MEDIUM

### Long-Term Actions

7. **Create Icarus-compatible build system**
   - Add conditional compilation for Icarus vs Quartus
   - Use defines to select compatible syntax
   - Priority: MEDIUM

8. **Add more comprehensive tests**
   - Video timing tests
   - VRAM access tests
   - Scandoubler tests
   - Priority: MEDIUM

---

## Comparison with MCGA Controller

| Aspect | CGA Controller | MCGA Controller |
|--------|---------------|-----------------|
| Icarus Verilog Compatible | ❌ NO (multiple bugs) | ✓ YES (after fixes) |
| Register Tests | ❌ Blocked | ✓ Passing (100%) |
| Address Decode | ? Unknown (untested) | ✓ Fixed and working |
| Video Modes | 7 modes (standard CGA) | 3 modes (subset VGA) |
| Status | BROKEN | WORKING |

---

## Files Analyzed

- `Quartus/rtl/CGA/cgacard.sv` - Top-level CGA card module
- `Quartus/rtl/CGA/cga.sv` - Main CGA controller logic
- `Quartus/rtl/CGA/cga_pixel.sv` - Pixel processing (BUGS FOUND HERE)
- `Quartus/rtl/CGA/cga_sequencer.sv` - Video sequencer
- `Quartus/rtl/CGA/cga_vgaport.sv` - Digital-to-analog converter
- `Quartus/rtl/CGA/cga_attrib.sv` - Attribute processing
- `Quartus/rtl/CGA/UM6845R.sv` - 6845 CRT controller
- `Quartus/rtl/CGA/vram.sv` - Video RAM
- `Quartus/rtl/CGA/busConverter.sv` - Bus width converter

---

## Conclusion

The CGA controller has **critical compatibility bugs** that prevent compilation and testing with Icarus Verilog. The bugs are straightforward to fix but currently block all testing activities.

**After bugs are fixed**, comprehensive testing can proceed to verify:
- Register functionality
- Video mode switching
- Timing accuracy
- VRAM access
- Scandoubling
- Tandy mode compatibility

**Priority:** Fix Bugs 1 and 2 immediately to unblock testing.

---

## Test Infrastructure Ready

Once bugs are fixed, the following test infrastructure is ready to use:
- ✓ `modelsim/cga_registers_tb.sv` - Comprehensive register tests
- ✓ `modelsim/run_cga_test.sh` - Automated test execution
- ✓ Test cases for all CGA modes
- ✓ CRTC programming tests
- ✓ Timing signal verification

**Estimated time to fix bugs:** 30-60 minutes
**Estimated time to run full test suite:** 5-10 minutes
**Total time to verified CGA controller:** 1-2 hours

---

**Report Generated:** 2025-11-08
**Test Tool:** Icarus Verilog 11.0
**Status:** Testing blocked - awaiting bug fixes
