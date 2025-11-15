# PC Speaker Connection Analysis - MiSTer Integration

## Executive Summary

**Status**: ❌ **NOT CONNECTED** - PC Speaker is completely disabled

**Impact**:
- ❌ No PC speaker beeps (POST codes, system beeps, BIOS errors)
- ❌ No speaker sound effects in DOS games
- ❌ No audio output from speaker-only applications
- ❌ Silent boot (no startup beep)

**Root Cause**: Speaker implementation exists but is completely disabled via commented-out `CONFIG_SPEAKER` defines

## PC Speaker Architecture

### Traditional IBM PC/XT Speaker Implementation

In a real IBM PC/XT, the speaker is controlled by:

```
PPI Port B (0x61):
  Bit 0: Timer 2 Gate Enable (gates timer output to speaker)
  Bit 1: Speaker Data (direct speaker control)

Timer 2 (8253 PIT):
  Channel 2: Generates square wave frequencies for speaker tones
  Output: speaker_timer_out

Final Speaker Output:
  speaker_out = (speaker_timer_out AND gate_enable) OR speaker_data
```

### This Implementation (FPGA)

**Alternative Design**: Speaker control through PS/2 Keyboard Controller

Instead of using PPI Port B bits 0-1, this implementation uses:
```
PS2KeyboardController Register (Port 0x60, Upper Byte):
  Bit 8: speaker_gate_en (equivalent to PPI Port B bit 0)
  Bit 9: speaker_data (equivalent to PPI Port B bit 1)
```

This is a **valid alternative approach** used in some PC designs where the keyboard controller (8042) also handles speaker control.

## Signal Path Analysis

### File: `/home/user/MyPC/Quartus/rtl/common/Top.sv`

#### Working Speaker Implementation (When CONFIG_SPEAKER Enabled)

**Lines 60-79** - Proper speaker signal routing:
```systemverilog
`ifdef CONFIG_SPEAKER

wire speaker_gate_en;
wire speaker_timer_out;
wire speaker_data;
assign speaker_out = speaker_timer_out & speaker_data;  // IBM PC compatible
`define SPEAKER_TIMER_OUT speaker_timer_out
`define SPEAKER_DATA speaker_data
`define SPEAKER_GATE_EN_OUT speaker_gate_en
`define SPEAKER_GATE_EN_IN speaker_gate_en

`else // CONFIG_SPEAKER

`define SPEAKER_TIMER_OUT        // Empty - resolves to nothing
`define SPEAKER_DATA_OUT         // Empty
`define SPEAKER_DATA             // Empty
`define SPEAKER_GATE_EN_OUT      // Empty
`define SPEAKER_GATE_EN_IN 1'b0  // Hardcoded low

`endif
```

**Line 670-671** - Timer connection:
```systemverilog
Timer Timer(.clk(sys_clk),
            ...
            .speaker_out(`SPEAKER_TIMER_OUT),      // Connects to speaker_timer_out
            .speaker_gate_en(`SPEAKER_GATE_EN_IN), // Connects to speaker_gate_en
            .*);
```

**Line 830-831** - PS2 Keyboard Controller connection:
```systemverilog
PS2KeyboardController #(.clkf(50000000))
    PS2KeyboardController(.clk(sys_clk),
                          ...
                          .speaker_gate_en(`SPEAKER_GATE_EN_OUT),  // Outputs gate control
                          .speaker_data(`SPEAKER_DATA),             // Outputs data control
                          .*);
```

**Status**: ✅ **Signal routing exists and is correct** (when enabled)

### File: `/home/user/MyPC/Quartus/mycore.sv`

#### MiSTer Integration Status

**Lines 509-528** - CONFIG_SPEAKER completely commented out:
```systemverilog
/*`ifdef CONFIG_SPEAKER           // <-- COMMENTED OUT!

wire speaker_gate_en;
wire speaker_timer_out;
wire speaker_data;
assign speaker_out = speaker_timer_out & speaker_data;
`define SPEAKER_TIMER_OUT speaker_timer_out
`define SPEAKER_DATA speaker_data
`define SPEAKER_GATE_EN_OUT speaker_gate_en
`define SPEAKER_GATE_EN_IN speaker_gate_en

`else // CONFIG_SPEAKER*/         // <-- Comment continues

`define SPEAKER_TIMER_OUT         // Empty macros (active)
`define SPEAKER_DATA_OUT
`define SPEAKER_DATA
`define SPEAKER_GATE_EN_OUT
`define SPEAKER_GATE_EN_IN 1'b0

/*`endif*/                         // <-- COMMENTED OUT!
```

**Effect**: All speaker signal macros resolve to empty/zero, disconnecting the entire speaker path.

**Lines 206-208** - Audio outputs hardcoded to silence:
```systemverilog
assign AUDIO_S = 0;
assign AUDIO_L = 0;    // ❌ Left audio channel: SILENT
assign AUDIO_R = 0;    // ❌ Right audio channel: SILENT
assign AUDIO_MIX = 0;
```

**Line 107** - Audio clock input (unused):
```systemverilog
input CLK_AUDIO,  // 24.576 MHz - Available but not used
```

## What Exists vs. What's Connected

### ✅ Hardware Components That Exist and Work

| Component | File | Status |
|-----------|------|--------|
| **Timer (8253 PIT)** | `rtl/KF8253/` | ✅ Fully functional (27/27 tests) |
| **Timer Channel 2** | Timer.sv | ✅ Outputs speaker_timer_out |
| **PS2 Keyboard Controller** | `rtl/ps2/PS2KeyboardController.sv` | ✅ Outputs speaker_gate_en & speaker_data |
| **Speaker Signal Combining** | Top.sv:65 | ✅ Logic exists: `speaker_out = timer & data` |
| **Audio Clock (24.576 MHz)** | MiSTer framework | ✅ Available on CLK_AUDIO input |

### ❌ What's Disconnected/Missing

| Component | Status | Issue |
|-----------|--------|-------|
| **CONFIG_SPEAKER define** | ❌ Commented out | Disables entire speaker subsystem |
| **speaker_out signal** | ❌ Not generated | Macros resolve to empty |
| **AUDIO_L output** | ❌ Hardcoded to 0 | No audio routing |
| **AUDIO_R output** | ❌ Hardcoded to 0 | No audio routing |
| **Speaker-to-Audio converter** | ❌ Missing | No 1-bit speaker → 16-bit PCM conversion |
| **PPI Port B bits 0-1** | ❌ Unused | Traditional speaker control path not implemented |

## MiSTer Audio Framework

The MiSTer framework provides:

**Audio Output Interface**:
```systemverilog
input         CLK_AUDIO,    // 24.576 MHz audio clock
output [15:0] AUDIO_L,      // 16-bit signed PCM, left channel
output [15:0] AUDIO_R,      // 16-bit signed PCM, right channel
output        AUDIO_S,      // 1 = signed samples, 0 = unsigned
output  [1:0] AUDIO_MIX,    // 0 = stereo, 1 = 25% mix, 2 = 50%, 3 = 100% (mono)
```

**Audio Sample Rate**: Typically 48 kHz (24.576 MHz / 512)

## What Needs to Be Implemented

### 1. Enable CONFIG_SPEAKER (Simple)

**File**: `mycore.sv` lines 509-528

**Current**:
```systemverilog
/*`ifdef CONFIG_SPEAKER
...
`else // CONFIG_SPEAKER*/

`define SPEAKER_TIMER_OUT
`define SPEAKER_DATA_OUT
`define SPEAKER_DATA
`define SPEAKER_GATE_EN_OUT
`define SPEAKER_GATE_EN_IN 1'b0

/*`endif*/
```

**Fixed**:
```systemverilog
`ifdef CONFIG_SPEAKER

wire speaker_gate_en;
wire speaker_timer_out;
wire speaker_data;
assign speaker_out = speaker_timer_out & speaker_data;
`define SPEAKER_TIMER_OUT speaker_timer_out
`define SPEAKER_DATA speaker_data
`define SPEAKER_GATE_EN_OUT speaker_gate_en
`define SPEAKER_GATE_EN_IN speaker_gate_en

`else // CONFIG_SPEAKER

`define SPEAKER_TIMER_OUT
`define SPEAKER_DATA_OUT
`define SPEAKER_DATA
`define SPEAKER_GATE_EN_OUT
`define SPEAKER_GATE_EN_IN 1'b0

`endif
```

**AND** add `-DCONFIG_SPEAKER` to Quartus compilation defines.

### 2. Create Speaker-to-Audio Converter (Complex)

**New Module Required**: `SpeakerAudioConverter.sv`

**Purpose**: Convert 1-bit speaker signal to 16-bit PCM audio samples

**Functionality**:
```systemverilog
module SpeakerAudioConverter (
    input  logic        clk_sys,          // System clock (50 MHz)
    input  logic        clk_audio,        // Audio clock (24.576 MHz)
    input  logic        reset,
    input  logic        speaker_in,       // 1-bit speaker signal
    input  logic [1:0]  volume,           // Volume control (0-3)
    output logic [15:0] audio_out_l,      // 16-bit PCM left
    output logic [15:0] audio_out_r       // 16-bit PCM right (mono = same as left)
);

// Implementation approach:
// 1. Cross speaker_in from sys_clk to clk_audio domain (BitSync)
// 2. Convert 1-bit to signed 16-bit: speaker ? volume_level : -volume_level
// 3. Optional low-pass filter to reduce aliasing
// 4. Sample at audio rate (48 kHz from 24.576 MHz / 512)

endmodule
```

**Volume Mapping** (from menu option "Speaker Volume,1,2,3,4"):
```
Volume 0: ±2048  (1/8 full scale, -42 dB)
Volume 1: ±4096  (1/4 full scale, -36 dB)
Volume 2: ±8192  (1/2 full scale, -30 dB)
Volume 3: ±16384 (full scale, -24 dB)
```

### 3. Connect Audio Outputs

**File**: `mycore.sv` lines 206-208

**Current**:
```systemverilog
assign AUDIO_S = 0;
assign AUDIO_L = 0;
assign AUDIO_R = 0;
assign AUDIO_MIX = 0;
```

**Fixed**:
```systemverilog
assign AUDIO_S = 1;              // Signed audio samples
assign AUDIO_L = speaker_audio;  // From SpeakerAudioConverter
assign AUDIO_R = speaker_audio;  // Mono speaker → both channels
assign AUDIO_MIX = 0;            // No mixing needed (mono source)
```

### 4. Wire Volume Control

**File**: `mycore.sv`

Extract volume from status register:
```systemverilog
wire [1:0] speaker_volume = status[1:0];  // From OSD menu bits o01
```

Pass to converter:
```systemverilog
SpeakerAudioConverter speaker_converter (
    .clk_sys(sys_clk),
    .clk_audio(CLK_AUDIO),
    .reset(post_sdram_reset),
    .speaker_in(speaker_out),
    .volume(speaker_volume),
    .audio_out_l(speaker_audio),
    .audio_out_r(speaker_audio)  // Mono
);
```

## Alternative: PC Speaker via PPI Port B (Optional)

**Traditional IBM PC Method**: Control speaker through PPI Port B bits 0-1

**Pros**:
- More authentic to original IBM PC/XT
- Software compatibility with PC/XT BIOS and DOS programs
- Standard PC architecture

**Cons**:
- Requires routing PPI port_b_out[1:0] to speaker control
- Current implementation uses PS/2 keyboard controller instead

**Implementation** (if desired):
```systemverilog
// In mycore.sv, replace PS/2 keyboard speaker control with PPI control:
wire speaker_gate_en = port_b_out[0];   // PPI Port B bit 0
wire speaker_data = port_b_out[1];      // PPI Port B bit 1
```

**Note**: Current PS/2 keyboard controller approach is also valid (used in some PC clones).

## Testing Requirements

After implementing speaker support:

### 1. Basic Functionality Tests
- **POST beep**: Verify startup beep on boot
- **BIOS error beeps**: Test error code beeps (memory errors, etc.)
- **DOS command**: `ECHO ^G` (Ctrl+G) should beep

### 2. Frequency Tests
- **Low frequency**: 100 Hz tone
- **Mid frequency**: 1000 Hz tone (typical beep)
- **High frequency**: 5000 Hz tone

### 3. Game Compatibility
- **Alley Cat**: Speaker sound effects
- **Digger**: Speaker music and effects
- **PC-Man**: Speaker sounds

### 4. Volume Control
- Verify OSD volume settings work (1-4 levels)
- Verify volume changes take effect immediately

## Resource Impact Estimate

**FPGA Resources** (SpeakerAudioConverter module):
- **ALMs**: ~100-200 (clock domain crossing, volume scaling, filtering)
- **M10K RAM**: 0 (no buffering needed)
- **DSP blocks**: 0 (simple multiplication by constant)

**Timing Impact**:
- Minimal (audio clock domain is separate from main 50 MHz)
- No impact on critical path

**Compilation Time**:
- +1-2 minutes (simple module)

## Current Configuration Menu

From CONF_STR (lines 265-267):
```
"P2o01,Speaker Volume,1,2,3,4;"    // status[1:0]
"P2o23,Tandy Volume,1,2,3,4;"      // status[3:2] (not implemented)
"P2o45,Audio Boost,No,2x,4x;"      // status[5:4] (not implemented)
"P2o67,Stereo Mix,none,25%,50%,100%;"  // status[7:6] (not implemented)
```

**Status**: Menu options exist but backend implementation missing

## Comparison: PS/2 Keyboard vs. PC Speaker

| Feature | PS/2 Keyboard | PC Speaker |
|---------|---------------|------------|
| **Input direction** | ✅ USB→FPGA working | ✅ Timer/PS2→speaker logic exists |
| **Output direction** | ✅ FPGA→USB **FIXED** | ❌ Speaker→Audio **NOT CONNECTED** |
| **Hardware exists** | ✅ Complete | ✅ Complete (timer, control signals) |
| **MiSTer integration** | ✅ hps_io PS/2 emulation | ❌ No audio output wired |
| **Config defines** | ✅ CONFIG_PS2 enabled | ❌ CONFIG_SPEAKER disabled |
| **User impact** | Minor (LED updates) | Major (no beeps/sound effects) |
| **Fix complexity** | ⭐ Trivial (2 lines) | ⭐⭐⭐ Moderate (new audio converter) |

## Conclusion

The PC speaker **hardware is fully implemented** in the FPGA (timer, control signals, logic gates), but:

1. ❌ **CONFIG_SPEAKER is disabled** - Commented out, making all signal macros empty
2. ❌ **Audio outputs hardcoded to 0** - No conversion from speaker signal to audio samples
3. ❌ **No speaker-to-audio converter** - Missing bridge from 1-bit speaker to 16-bit PCM
4. ❌ **Audio clock unused** - CLK_AUDIO available but not utilized

**To enable PC speaker**:
1. ✅ **Simple**: Uncomment CONFIG_SPEAKER defines (enables signal generation)
2. ⭐⭐ **Medium**: Create SpeakerAudioConverter module (~100 lines)
3. ⭐ **Simple**: Wire converter output to AUDIO_L/AUDIO_R
4. ⭐ **Simple**: Connect volume control from OSD menu

**Estimated Implementation Time**: 2-4 hours for experienced FPGA developer

**Payoff**: Authentic PC speaker beeps, game sound effects, POST codes - significant authenticity improvement for PC/XT emulation.

---

**Analysis Date**: 2025-11-15
**Analyzed By**: Claude (Anthropic)
**Files Examined**:
- `/home/user/MyPC/Quartus/mycore.sv` (2234 lines)
- `/home/user/MyPC/Quartus/rtl/common/Top.sv` (848 lines)
- `/home/user/MyPC/Quartus/rtl/ps2/PS2KeyboardController.sv` (128 lines)
- `/home/user/MyPC/Quartus/rtl/KF8253/Timer.sv`
- MiSTer framework audio interface documentation
