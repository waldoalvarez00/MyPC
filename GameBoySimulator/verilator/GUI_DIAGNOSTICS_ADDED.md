# GUI Diagnostics Added

**Date:** December 9, 2025
**Status:** Comprehensive diagnostics implemented

## Problem

The GUI simulator was experiencing `ce_cpu=0` stuck at 0, preventing CPU execution and LCD output. To diagnose this issue, comprehensive real-time diagnostics have been added.

## New Features Added

### 1. Real-Time Clock & State Diagnostic Window

**Location:** New window at position (510, 0)
**Size:** 350x400 pixels

**Displays:**

#### CLOCK SIGNALS
- `clk_sys` - System clock state (0/1)
- `ce_cpu` - CPU clock enable (**[PULSING]** or **[STUCK!]**)
- `ce_cpu2x` - 2x CPU clock enable

#### CORE STATE
- `reset` - Reset signal (**[ASSERTED]** or **[RELEASED]**)
- `main_time` - Current simulation cycle count
- `simulation FPS` - Frame rate

#### BOOT & CART
- `boot_rom_enabled` - Boot ROM active (**[BOOT ROM]** or **[CART ROM]**)
- `sel_boot_rom` - Boot ROM selection signal
- `cart_ready` - Cart ready state (**[READY]** or **[NOT READY]**)
- `cart_download` - Cart download in progress

#### CPU STATE
- `cpu_addr` - CPU address bus (hex)
- `cpu_rd_n` - CPU read signal (IDLE/READING)
- `cart_rd` - Cart read signal
- `cart_wr` - Cart write signal

#### LCD STATE
- `lcd_mode` - LCD mode (0=HBlank, 1=VBlank, 2=OAM, 3=Transfer)
- `VGA_HB` - Horizontal blank
- `VGA_VB` - Vertical blank
- `VGA_HS` - Horizontal sync
- `VGA_VS` - Vertical sync

### 2. Clock Enable Pulse Test Function

**Function:** `testClockEnable()`

**What it does:**
1. Monitors `ce_cpu` for 1000 clock cycles
2. Counts:
   - Times `ce_cpu=1` (high)
   - Times `ce_cpu=0` (low)
   - Rising edges (0→1 transitions)
3. Reports findings

**Expected Results:**
- **Normal:** ~60 rising edges in 1000 cycles
- **Stuck:** 0 rising edges
- **Abnormal:** < 10 rising edges

**Output Example (Normal):**
```
=== CE_CPU PULSE TEST ===
  Initial ce_cpu: 0
  After 1000 cycles:
    ce_cpu=1 count: 125
    ce_cpu=0 count: 875
    Rising edges: 62
  [PASS] ce_cpu is pulsing normally
  Current signals:
    reset: 0
    ce_cpu: 1
    ce_cpu2x: 1
    cpu_addr: 0x0012
```

**Output Example (Stuck):**
```
=== CE_CPU PULSE TEST ===
  Initial ce_cpu: 0
  After 1000 cycles:
    ce_cpu=1 count: 0
    ce_cpu=0 count: 1000
    Rising edges: 0
  [FAIL] ce_cpu NEVER PULSED!
  Problem: Clock divider not generating ce_cpu
  Current signals:
    reset: 0
    ce_cpu: 0
    ce_cpu2x: 0
    cpu_addr: 0x0000
```

### 3. Manual Diagnostic Buttons

**Location:** Simulation Control window
**Buttons added:**

1. **"Test ce_cpu Pulse"** - Manually trigger clock enable test
2. **"Verify ROM"** - Verify ROM loaded in SDRAM

**Usage:**
- Click buttons at any time during simulation
- Results appear in Debug Log window
- Can be run repeatedly to check state changes

### 4. Automatic Diagnostic on Startup

**When:** Runs once after initialization (first diagnostic cycle)

**Tests performed:**
1. TEST 1: ROM in SDRAM (verify Nintendo logo)
2. TEST 2: Reset state
3. TEST 3: Clock enable pulses (**NEW!**)

Results automatically logged to Debug Log window on startup.

## How to Use the Diagnostics

### Visual Monitoring

1. **Launch the simulator**
2. **Look at "Clock & State Diagnostics" window** (top right)
3. **Key indicators:**
   - `ce_cpu: 0 [STUCK!]` = **PROBLEM!** Clock divider not working
   - `ce_cpu: 1 [PULSING]` = Good (but should alternate, not stay 1)
   - `reset: 1 [ASSERTED]` = CPU held in reset
   - `boot_rom_enabled: 1 [BOOT ROM]` = Boot ROM active
   - `cart_ready: 0 [NOT READY]` = Cart not loaded

### Manual Testing

1. **Click "Test ce_cpu Pulse"** button
2. **Check Debug Log** for results
3. **Look for:**
   - "ce_cpu NEVER PULSED!" = Clock divider problem
   - "ce_cpu pulsed only X times" = Clock divider weak/slow
   - "ce_cpu is pulsing normally" = Clock divider OK

### What to Report

If still having issues, report these values:

**From Clock & State Diagnostics window:**
```
ce_cpu: X [STATUS]
reset: X [STATUS]
boot_rom_enabled: X [STATUS]
cart_ready: X [STATUS]
cpu_addr: 0xXXXX
lcd_mode: X
```

**From Test ce_cpu Pulse (Debug Log):**
```
ce_cpu=1 count: X
ce_cpu=0 count: X
Rising edges: X
[PASS/FAIL/WARN]
```

**From Console Log:**
```
Clock divider started, ce_cpu=X
```

## Troubleshooting Guide

### Issue: ce_cpu=0 constantly

**Check:**
1. Is reset=1? ✓ Expected during startup
2. After reset=0, does ce_cpu pulse? Test with button
3. What does console log show for "Clock divider started, ce_cpu=X"?

**Possible causes:**
- Clock divider not initializing (reset timing issue)
- Clock divider stuck (hardware bug)
- Clock source not running (clk_sys problem)

### Issue: boot_rom_enabled=1 never changes

**Check:**
1. Is ce_cpu pulsing? Must pulse for CPU to execute
2. Is cpu_addr changing? Shows CPU executing
3. Did boot ROM disable itself? Writes to $FF50

**Possible causes:**
- CPU not executing (ce_cpu stuck)
- Boot ROM stuck in loop
- Boot ROM disable mechanism broken

### Issue: LCD shows nothing (lcd_mode=0)

**Check:**
1. Is boot_rom_enabled=0? Must transition to cart
2. Is cpu_addr in cart range? (0x0100+)
3. Are VGA signals changing? (HB, VB, HS, VS)

**Possible causes:**
- CPU not reaching cart code
- LCD not initialized by boot ROM
- LCD registers not programmed

## Files Modified

### `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/sim_main_gui.cpp`

**Changes:**

1. **Lines ~537-588:** Added `testClockEnable()` function
   - Monitors ce_cpu for 1000 cycles
   - Reports pulse count and status

2. **Lines ~1012-1055:** Added Clock & State Diagnostics window
   - Real-time display of all key signals
   - Color-coded status indicators

3. **Lines ~658-660:** Added TEST 3 to startup diagnostics
   - Automatically tests ce_cpu on first run

4. **Lines ~1054-1061:** Added manual diagnostic buttons
   - Test ce_cpu Pulse button
   - Verify ROM button

## Expected Behavior After This Update

### On Startup

1. Console log shows:
   ```
   Initialization cycles complete under reset
   Loaded DMG boot ROM from: ...
   Downloading DMG boot ROM...
   Boot ROM download complete
   Clock divider started, ce_cpu=1  ← Should be 1!
   Simulating cart download...
   cart_ready set after 1 writes
   GameBoy initialization complete, cart_ready=1
   ```

2. Diagnostic tests run:
   ```
   TEST 1: ROM in SDRAM
     PASS: Nintendo logo detected!
   TEST 2: Reset state
     Reset signal: 1
   TEST 3: Clock enable pulses
     [PASS/FAIL] ...
   ```

3. Clock & State window shows:
   - `ce_cpu` alternating or showing status
   - `reset` transitioning 1→0
   - `boot_rom_enabled` transitioning 1→0
   - `lcd_mode` changing from 0

### During Execution

- Clock & State window updates in real-time
- All signals visible
- Can click "Test ce_cpu Pulse" to verify at any time

## Next Steps

1. **Build the updated simulator**
2. **Launch and observe:**
   - Clock & State Diagnostics window
   - Debug Log output
3. **Report findings:**
   - What does TEST 3 show?
   - What is ce_cpu status in diagnostic window?
   - What does "Clock divider started, ce_cpu=X" show?

This information will pinpoint exactly where the clock divider initialization is failing.

---

**Status:** ✅ Diagnostics implemented and ready for testing
