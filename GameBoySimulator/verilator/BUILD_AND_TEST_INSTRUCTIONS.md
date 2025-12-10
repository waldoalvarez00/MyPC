# GameBoy Simulator - Build and Test Instructions

**Status:** ✅ Critical clock edge fix applied
**Date:** December 9, 2025

## What Was Fixed

The GUI simulator had a **critical clock simulation bug** that prevented the GameBoy's clock divider from generating `ce_cpu` pulses. This caused the CPU to stall with `ce_cpu=0` stuck at 0, resulting in no LCD output.

**Root Cause:** The simulator only evaluated one clock edge per cycle instead of both rising and falling edges.

**Fix Applied:** All clock simulation now uses proper two-edge evaluation matching the working CLI tests.

See `CLOCK_EDGE_FIX.md` for detailed technical explanation.

## Files Modified

### `/mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator/sim_main_gui.cpp`

**Fixed sections:**
1. Main `verilate()` function - simulation loop
2. `downloadBootROM()` function - boot ROM download loops
3. `simulateCartDownload()` function - cart download loops
4. `testClockEnable()` function - diagnostic test loop
5. Initialization sequence - three initialization loops
6. `resetSim()` function - reset loop

**Total changes:** ~150 lines modified across 8 locations

## Build Instructions (Windows)

### Option 1: Visual Studio

1. **Open the project:**
   ```
   Open: GameBoySimulator/verilator/sim.vcxproj
   ```

2. **Select configuration:**
   - Configuration: `Debug` or `Release`
   - Platform: `x64`

3. **Build:**
   - Menu: `Build → Build Solution` (Ctrl+Shift+B)
   - OR right-click project → Build

4. **Expected output:**
   ```
   Build succeeded.
   0 Errors, 0 Warnings
   ```

5. **Executable location:**
   ```
   GameBoySimulator/verilator/x64/Debug/sim.exe
   OR
   GameBoySimulator/verilator/x64/Release/sim.exe
   ```

### Option 2: MSBuild (Command Line)

```cmd
cd GameBoySimulator\verilator
"C:\Program Files\Microsoft Visual Studio\2022\Community\MSBuild\Current\Bin\MSBuild.exe" sim.vcxproj /p:Configuration=Release /p:Platform=x64
```

## Run Instructions

### Basic Run (Use existing game.gb)

```cmd
cd GameBoySimulator\verilator\x64\Release
.\sim.exe
```

The simulator will load `./game.gb` by default if it exists.

### Run with Custom ROM

```cmd
.\sim.exe path\to\your_rom.gb
```

### Run with Demo ROM

```cmd
.\sim.exe demo.gb
```

## What to Expect After Fix

### 1. Console Log Output

```
=== GAMEBOY SIMULATOR GUI ===
ROM loaded: game.gb (32768 bytes)
Loading ROM into SDRAM...
Initialization cycles complete under reset
Loaded DMG boot ROM from: gameboy_core/BootROMs/bin/dmg_boot.bin
Downloading DMG boot ROM (256 bytes)...
Boot ROM download complete (128 words written)
Clock divider started, ce_cpu=1  ← Should show 1!
Simulating cart download to trigger cart_ready...
  cart_ready set after 1 writes
Cart download simulation complete, cart_ready=1
GameBoy initialization complete, cart_ready=1

=== STARTING DIAGNOSTICS ===
TEST 1: ROM in SDRAM
  Reading from 0x104-0x133 (Nintendo logo area)...
  PASS: Nintendo logo detected!

TEST 2: Reset state
  Reset signal: 1

TEST 3: Clock enable pulses
  Initial ce_cpu: 0
  After 1000 cycles:
    ce_cpu=1 count: 60-80        ← Should be 60-80!
    ce_cpu=0 count: 920-940
    Rising edges: 60-80          ← Should be 60-80!
  [PASS] ce_cpu is pulsing normally  ← Should PASS!
  Current signals:
    reset: 1
    ce_cpu: 0
    cpu_addr: 0x0000

Reset released at cycle 48
  boot_rom_enabled status: 1
```

### 2. GUI Windows

**Clock & State Diagnostics Window** (top right):
```
=== CLOCK SIGNALS ===
clk_sys: 1
ce_cpu:  1  [PULSING]  ← Should alternate, not stuck!

=== CORE STATE ===
reset: 0  [RELEASED]
main_time: 150
simulation FPS: 60.0

=== BOOT & CART ===
boot_rom_enabled: 1  [BOOT ROM]  ← Should change to 0 after boot
sel_boot_rom: 1
cart_ready: 1  [READY]
cart_download: 0

=== CPU STATE ===
cpu_addr: 0x0012  ← Should change as CPU executes
cpu_rd_n: 0  READING
cart_rd: 1
cart_wr: 0

=== LCD STATE ===
lcd_mode: 2  ← Should change (0=HBlank, 1=VBlank, 2=OAM, 3=Transfer)
VGA_HB: 0
VGA_VB: 0
```

**Video Window:**
- Should show GameBoy LCD output (160x144 scaled)
- Boot ROM: Nintendo logo scrolls down, plays "ding" sound
- Game ROM: Game should start after boot

**Control Window:**
- Click "Start running" if not already running
- main_time counter should increment steadily
- frame_count should increment

### 3. Execution Timeline

**0-48 cycles:** Reset asserted
- CPU held in reset
- ce_cpu may not pulse yet
- boot_rom_enabled=1

**48-500 cycles:** Boot ROM execution
- ce_cpu pulses every ~16 cycles
- CPU executes boot ROM code
- Nintendo logo scrolls (real boot ROM) OR immediate disable (minimal boot)
- boot_rom_enabled=1→0 transition

**500+ cycles:** Game execution
- boot_rom_enabled=0
- CPU executes cart ROM from 0x0100
- LCD initializes and displays game graphics
- Video output appears in window!

## Troubleshooting

### Issue: Still shows ce_cpu=0 stuck

**Check:**
1. Did you rebuild after pulling changes?
2. Is the correct executable running? (Check build date)
3. Try cleaning and rebuilding: `Build → Clean Solution` then rebuild

**Verify fix applied:**
Look for comment in sim_main_gui.cpp around line 813:
```cpp
// OLD CODE used clk_sys.Tick() which only evaluated once per toggle
```
If this comment exists, the fix was applied.

### Issue: Build errors

**Common errors:**

1. **Missing obj_dir files:**
   - Re-run verilate script on Linux/WSL
   - Copy updated obj_dir files to Windows

2. **Stale obj_dir files:**
   - Delete obj_dir/*.cpp
   - Re-run verilate_gameboy.sh

3. **Missing headers:**
   - Check all `sim/` files present
   - Check `obj_dir/Vtop*.h` files present

### Issue: Crash on startup

**Check:**
1. ROM file exists and is valid GameBoy ROM
2. SDRAM model initialized (should auto-initialize)
3. Console window for error messages

### Issue: Black screen but no errors

**Check:**
1. Is "RUN" checkbox enabled in Control window?
2. Is main_time increasing?
3. Is frame_count increasing in Video window?
4. Click "Test ce_cpu Pulse" button - does it show [PASS]?

### Issue: Display but wrong graphics

**This is expected if:**
- Using a ROM that expects specific initialization
- ROM needs boot ROM sequence (try with real dmg_boot.bin)
- ROM has bugs or is corrupted

## Performance Notes

### Expected Performance

- **Simulation speed:** ~24 MHz effective (vs 64 MHz real-time)
- **Frame rate:** 60 FPS (or close)
- **Batch size:** 150,000 cycles per GUI frame (default)

### Adjusting Performance

**In Control window:**
- **Run batch size slider:** Increase for faster simulation (but slower GUI updates)
- Typical range: 50,000 - 250,000
- Larger batches = faster simulation but less responsive GUI

### System Requirements

- **CPU:** Modern x64 processor (simulation is CPU-intensive)
- **RAM:** 2-4 GB minimum
- **GPU:** Any with DirectX 11 support (for ImGui rendering)

## Testing Checklist

After building and running:

- [ ] Simulator starts without errors
- [ ] Console log shows "ce_cpu=1" during initialization
- [ ] TEST 3 shows **[PASS]** with 60-80 rising edges
- [ ] Clock & State window shows `ce_cpu` alternating
- [ ] main_time counter increments
- [ ] boot_rom_enabled transitions from 1→0
- [ ] cpu_addr changes as CPU executes
- [ ] lcd_mode changes from 0
- [ ] **VIDEO OUTPUT APPEARS** in Video window!

## Success Criteria

✅ **Fix successful if:**
1. Console log: `ce_cpu=1` during initialization
2. TEST 3: `[PASS] ce_cpu is pulsing normally`
3. Diagnostic window: `ce_cpu` shows `[PULSING]` not `[STUCK!]`
4. Video window displays GameBoy graphics
5. CPU address changes steadily
6. LCD mode transitions (not stuck at 0)

## Additional Documentation

- **CLOCK_EDGE_FIX.md** - Detailed technical explanation of the fix
- **GUI_DIAGNOSTICS_ADDED.md** - Explanation of diagnostic features
- **GUI_BOOT_FIX.md** - Previous boot ROM fix attempt (superseded)
- **VS_BUILD_FIXES.md** - Visual Studio build error fixes

## Support

If issues persist after confirming the fix is applied:

1. **Capture diagnostic output:**
   - Console log (first 100 lines)
   - TEST 3 results
   - Clock & State window values

2. **Report:**
   - ce_cpu value during initialization
   - Rising edge count from TEST 3
   - Any error messages
   - Build configuration (Debug/Release)

---

**Expected Outcome:** GameBoy simulator displays video output on LCD with working CPU execution and proper clock enable pulses.
