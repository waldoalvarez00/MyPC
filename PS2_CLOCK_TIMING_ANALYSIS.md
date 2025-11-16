# PS/2 Controller Clock and Timing Analysis for MiSTer

## Executive Summary

**CRITICAL FINDING**: The PS/2 testbenches are testing the WRONG controllers with the WRONG clock frequency!

- **Actual MiSTer Hardware**: Uses `KFPS2KB` (keyboard) and `MSMouseWrapper` (mouse) at **30 MHz**
- **Testbenches**: Test `PS2KeyboardController` and `PS2MouseController` assuming **50 MHz**
- **Status**: `PS2KeyboardController` and `PS2MouseController` are **NOT USED** in the MiSTer build!

## MiSTer Hardware Configuration (mycore.sv - ACTUAL)

### PLL Configuration

```systemverilog
pll pll (
    .refclk(CLK_50M),           // Input: 50 MHz from MiSTer
    .rst(0),
    .outclk_0(sys_clk),         // 30.0 MHz ← SYSTEM CLOCK
    .outclk_1(vga_clk),         // 25.116279 MHz (VGA pixel clock)
    .outclk_2(pit_clk),         // 1.193058 MHz (PIT/Timer)
    .outclk_3(),                // 150 MHz (SignalTap debug)
    .outclk_4(clk_mem),         // 120 MHz (SDRAM)
    .outclk_5(clk_uart),        // UART clock
    .locked(plock)
);
```

**Source**: `/home/user/MyPC/Quartus/rtl/pll.v` lines 79-97
- `gui_output_clock_frequency0" value="30.0"` → sys_clk = 30 MHz
- `gui_reference_clock_frequency" value="50.0"` → CLK_50M input

### Keyboard Controller (ACTUAL - Used in MiSTer)

**Module**: `KFPS2KB` (NOT PS2KeyboardController!)

```systemverilog
KFPS2KB u_KFPS2KB (
    .clock                (sys_clk),           // 30 MHz
    .peripheral_clock     (sys_clk),           // 30 MHz
    .reset                (post_sdram_reset),
    .device_clock         (wps2_kbd_clk_2),    // PS/2 clock from HPS
    .device_data          (wps2_kbd_data_2),   // PS/2 data from HPS
    .irq                  (ps2_kbd_intr),
    .keycode              (keycode_buf),
    ...
);
```

**Location**: `/home/user/MyPC/Quartus/mycore.sv` lines 2098-2118
**Implementation**: `/home/user/MyPC/Quartus/rtl/Keyboard/KFPS2KB.sv`

**Key Differences from PS2KeyboardController**:
- Different scancode translation (PS/2 Set 2 → PC Set 1)
- Different register interface
- No CLKFREQ parameter (uses clock signals directly)
- Different FIFO mechanism

### Mouse Controller (ACTUAL - Used in MiSTer)

**Module**: `MSMouseWrapper` (NOT PS2MouseController!)

```systemverilog
MSMouseWrapper #(
    .CLKFREQ(30_000_000)  // ← 30 MHz clock frequency
) MSMouseWrapper_inst (
    .clk(sys_clk),                    // 30 MHz
    .ps2dta_in  (wps2_mouse_data_in),
    .ps2clk_in  (wps2_mouse_clk_in),
    .ps2dta_out (wps2_mouse_data_out),
    .ps2clk_out (wps2_mouse_clk_out),
    .rts(~rts_n),
    .rd(uart1_tx)
);
```

**Location**: `/home/user/MyPC/Quartus/mycore.sv` lines 1464-1474
**Clock Parameter**: Explicitly configured for 30 MHz

## Alternative Configuration (Top.sv - NOT USED)

### PS/2 Controllers (Disabled - Behind CONFIG_PS2 ifdef)

**Module**: `PS2KeyboardController` (UNUSED IN MISTER!)

```systemverilog
`ifdef CONFIG_PS2
PS2KeyboardController #(.clkf(50000000))  // ← Assumes 50 MHz
    PS2KeyboardController(
        .clk(sys_clk),
        .cs(ps2_kbd_access),
        ...
    );

PS2MouseController #(.clkf(50000000))     // ← Assumes 50 MHz
    PS2MouseController(
        .clk(sys_clk),
        .cs(ps2_mouse_access),
        ...
    );
`endif
```

**Location**: `/home/user/MyPC/Quartus/rtl/common/Top.sv` lines 823-844
**Status**: `CONFIG_PS2` is **NEVER DEFINED** → These modules are NOT compiled into MiSTer!

## Testbench Analysis

### Current Testbench Configuration

**PS/2 Keyboard Protocol Testbench**:
```systemverilog
PS2KeyboardController #(.clkf(50000000)) dut (
    .clk(clk),  // 50 MHz clock generated in testbench
    ...
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 20ns period = 50 MHz
end
```

**Location**: `/home/user/MyPC/modelsim/ps2_keyboard_protocol_tb.sv`

**PS/2 Mouse Testbench**:
```systemverilog
PS2MouseController #(.clkf(50000000)) dut (
    .clk(clk),  // 50 MHz assumed
    ...
);
```

**Location**: `/home/user/MyPC/modelsim/ps2_mouse_tb.sv`

### Problems Identified

1. **Wrong Module**: Testing `PS2KeyboardController` instead of `KFPS2KB`
2. **Wrong Frequency**: Using 50 MHz instead of actual 30 MHz
3. **Wrong Interface**: CPU interface vs. direct keycode interface
4. **Not in Build**: These modules aren't even compiled in the MiSTer build!

## Timing Parameter Analysis

### PS/2 Protocol Timing (Independent of System Clock)

The PS/2 protocol timing is **independent** of the system clock frequency:

**PS/2 Clock**: 10-16.7 kHz (60-100 μs period)
- **Device-to-Host**: Keyboard/mouse generates clock
- **Host-to-Device**: Host generates clock (inhibit period: 60-100 μs minimum)

**PS/2 Data Sampling**:
- Host samples data on **falling edge** of PS/2 clock
- Timing determined by PS/2 clock, not system clock

**System Clock Requirements**:
- Must be >> PS/2 clock for reliable sampling
- **30 MHz**: 33.3 ns period → **1800x faster** than PS/2 clock (60 μs)
- **50 MHz**: 20 ns period → **3000x faster** than PS/2 clock
- **Both frequencies are adequate** for PS/2 protocol

### Clock Frequency Impact

#### MSMouseWrapper Timing

The `CLKFREQ` parameter affects internal timeout counters:

```systemverilog
localparam tx_clock_inhibit_reload = (clkf / 1000000) * 100;
```

**At 50 MHz** (wrong):
- Inhibit reload = (50,000,000 / 1,000,000) × 100 = 5,000 cycles
- Inhibit time = 5,000 × 20ns = 100 μs ✓ Correct

**At 30 MHz** (correct):
- Inhibit reload = (30,000,000 / 1,000,000) × 100 = 3,000 cycles
- Inhibit time = 3,000 × 33.3ns = 100 μs ✓ Correct

**Conclusion**: Both work correctly for PS/2 protocol timing, but the parameter MUST match actual clock!

## Impact Assessment

### What Works Despite Configuration Mismatch

✅ **PS/2 Protocol Tests Still Valid**:
- Protocol timing tests (start/stop/parity bits) are still meaningful
- BitSync synchronizer tests are valid (works at both frequencies)
- FIFO tests are clock-frequency independent

### What's Potentially Wrong

⚠️ **Timeout Calculations**:
- Internal timeout counters are scaled by clock frequency
- 50 MHz testbench has 1.67x longer timeout periods than actual hardware
- May not catch timing bugs that appear at 30 MHz

⚠️ **Module Mismatch**:
- `PS2KeyboardController` has different architecture than `KFPS2KB`
- Different scancode translation tables
- Different register interfaces
- **Testing the wrong module entirely!**

## Recommendations

### Immediate Actions Required

1. **Create KFPS2KB Testbench**:
   - Test the ACTUAL keyboard controller used in MiSTer
   - Use 30 MHz system clock
   - Test keycode interface (not CPU register interface)

2. **Update MSMouseWrapper Tests**:
   - Change CLKFREQ parameter from 50,000,000 to 30,000,000
   - Verify timeout calculations at correct frequency

3. **Update Existing PS2KeyboardController Tests**:
   - Change clock from 50 MHz to 30 MHz
   - Add note that this module is NOT used in MiSTer
   - Keep tests for reference/alternative configurations

### Configuration Matrix

| Module | Used in MiSTer? | Clock Freq | Testbench Exists | Clock Correct |
|--------|-----------------|------------|------------------|---------------|
| KFPS2KB (keyboard) | ✅ YES | 30 MHz | ❌ NO | N/A |
| MSMouseWrapper (mouse) | ✅ YES | 30 MHz | ✅ YES | ⚠️ NO (uses 50 MHz) |
| PS2KeyboardController | ❌ NO (disabled) | 50 MHz* | ✅ YES | ⚠️ YES but wrong module |
| PS2MouseController | ❌ NO (disabled) | 50 MHz* | ✅ YES | ⚠️ YES but wrong module |

*If enabled in Top.sv, would use whatever sys_clk provides

### Priority Actions

**HIGH PRIORITY**:
1. Test KFPS2KB (actual keyboard controller) - **NO TESTS EXIST!**
2. Fix MSMouseWrapper testbench clock frequency

**MEDIUM PRIORITY**:
3. Document that PS2KeyboardController/PS2MouseController are unused
4. Consider adding Top.sv integration test with CONFIG_PS2 enabled

**LOW PRIORITY**:
5. Keep existing PS/2 protocol tests as reference implementations

## Conclusion

The current PS/2 testbenches are testing **hardware that doesn't exist in the MiSTer build** with **incorrect clock frequencies**. While the PS/2 protocol tests are still valuable for understanding the protocol, they do NOT verify the actual MiSTer hardware.

**Action Required**: Create proper testbenches for KFPS2KB and MSMouseWrapper at 30 MHz.
