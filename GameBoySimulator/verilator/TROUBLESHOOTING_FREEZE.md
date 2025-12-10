# Troubleshooting GUI Freeze / 0 FPS

**Issue:** Emulator appears stuck, no screen output, 0 FPS
**Date:** December 9, 2025

## Diagnostic Steps

### Step 1: Check if GUI is Responsive

**Try these actions:**
1. **Move the window** - Can you drag the title bar?
2. **Click buttons** - Do they respond to clicks?
3. **Hover over sliders** - Does the cursor change?

**Results:**
- **GUI responds:** Go to Step 2 (Simulation not running)
- **GUI frozen:** Go to Step 3 (GUI deadlock/crash)

---

## Step 2: GUI Responsive but Nothing Happening

This is the **most likely scenario**. The simulation is simply not running.

### Check #1: Is Simulation Running?

**Look at the Control window:**

1. **RUN checkbox** - Is it checked? ☐ or ☑?
   - If **unchecked**: Click **"Start running"** button or check the box
   - This is likely the issue - simulation starts **paused by default**

2. **main_time counter** - What does it show?
   - If **0 and not changing**: Simulation hasn't started
   - If **increasing**: Simulation is running (go to Check #2)

### Check #2: Batch Size Too Small?

**Look at Control window:**
- Current batch size value?
- Try sliding to **250,000** for faster simulation

### Check #3: Window Messages

**Console window should show:**
```
Initialization cycles complete under reset
Clock divider started, ce_cpu=1
GameBoy initialization complete, cart_ready=1
TEST 3: [PASS] ce_cpu is pulsing normally
```

If you see this, initialization worked. Now simulation just needs to run.

### Solution for Step 2

**To start simulation:**
1. Click **"Start running"** button in Control window
2. OR check the **"RUN"** checkbox
3. Watch main_time counter start increasing
4. Wait 20-30 seconds for boot to complete
5. Video should appear after ~10 seconds

---

## Step 3: GUI Completely Frozen

This indicates a crash, deadlock, or infinite loop.

### Likely Causes

1. **Missing ROM file** - But this should show error, not freeze
2. **SDRAM model issue** - Possible infinite loop in processSDRAM()
3. **Diagnostic code race condition** - Unlikely but possible

### Emergency Fix: Disable Diagnostics

If the GUI is frozen, we may need to disable the diagnostic code I added.

**Edit sim_main_gui.cpp around line 837-847 and comment out:**
```cpp
// TEMPORARILY DISABLED - testing for freeze
/*
// Track ce_cpu edges for diagnostics
if (top->dbg_ce_cpu && !last_ce_cpu_state) {
    ce_cpu_edges_count++;
}
last_ce_cpu_state = top->dbg_ce_cpu;

// Reset edge counter every 1000 cycles for display
if (main_time - ce_cpu_window_start >= 1000) {
    ce_cpu_window_start = main_time;
    ce_cpu_edges_count = 0;
}
*/
```

Then rebuild and try again.

### Debugging Tools (Windows)

**If GUI is frozen:**

1. **Task Manager** (Ctrl+Shift+Esc)
   - Is process using CPU? (Should be ~25% on 4-core)
   - Is process responding? (Should show "Not Responding" if frozen)

2. **Process Explorer** (if installed)
   - Check thread states
   - Look for deadlocked threads

3. **Visual Studio Debugger**
   - Attach to running process
   - Break execution (Debug → Break All)
   - Look at call stack to see where it's stuck

---

## Step 4: Expected Behavior When Working

### During Startup (First 1-2 seconds)

**Console window:**
```
ROM loaded: ./game.gb (65536 bytes)
Initialization cycles complete under reset
Clock divider started, ce_cpu=1  ← Should be 1!
TEST 3: [PASS] ce_cpu is pulsing normally  ← Should PASS!
```

**Control window:**
- RUN checkbox: ☐ (unchecked by default)
- main_time: 0
- Buttons: All responsive

**Clock & State Diagnostics window:**
```
ce_cpu: 0 [PULSING] (62 edges/1Kcyc)  ← Should show PULSING
reset: 1 [ASSERTED]
main_time: 0 (0.0M)
```

### After Clicking "Start running" (0-10 seconds)

**Control window:**
- RUN checkbox: ☑ (checked)
- main_time: **Rapidly increasing** (1000, 5000, 100000, 1M, 10M...)

**Clock & State Diagnostics window:**
```
ce_cpu: 0 [PULSING] (62 edges/1Kcyc)
reset: 0 [RELEASED]
main_time: 5234567 (5.2M)  ← Increasing!
SDRAM: R=0 W=increasing
boot_rom_enabled: 1 [BOOT ROM]
```

**Video window:**
- Shows "main_time: XXXXXXX frame_count: Y"
- main_time increasing rapidly
- frame_count: 0 (no video yet)

### After Boot Completes (10-15 seconds)

**Clock & State Diagnostics window:**
```
boot_rom_enabled: 0 [CART ROM]  ← Changed!
cpu_addr: 0x0100+  ← In cart ROM range
SDRAM: R=1000+ W=500+  ← Activity!
lcd_mode: 2  ← Not 0!
```

**Video window:**
- Frame count increasing (1, 2, 3, 4...)
- **Video output appears!** (GameBoy screen)

---

## Most Common Issue

**9 out of 10 times, the issue is:**

**RUN checkbox is unchecked by default!**

**Solution:**
1. Click **"Start running"** button
2. Wait 20-30 seconds
3. Video appears

---

## Quick Checklist

Before reporting a freeze, verify:

- [ ] RUN checkbox is **checked**
- [ ] main_time is **increasing**
- [ ] Console shows TEST 3 **PASS**
- [ ] Batch size is set to **150000-250000**
- [ ] Let it run for at least **30 seconds**
- [ ] Check Task Manager - is process using CPU?

If all of these check out and still no video after 60 seconds, there may be a deeper issue.

---

## Advanced: If Still Stuck After 60 Seconds

**Check these values in Clock & State Diagnostics:**

1. **ce_cpu edges:** Should be 60-63
   - If 0: Clock divider broken (shouldn't happen after TEST 3 pass)
   - If <10: Clock divider running very slow

2. **main_time:** Should be >100M
   - If <10M: Simulation running too slow, increase batch size
   - If stuck at specific value: Check for infinite loop

3. **boot_rom_enabled:** Should transition 1→0
   - If stuck at 1 after 100M cycles: Boot ROM infinite loop (ROM corruption?)
   - If stuck at 0 but no video: LCD init issue

4. **SDRAM reads:** Should be >0 after boot
   - If always 0: CPU not accessing memory properly
   - Check cart_ready=1, check cpu_addr changing

5. **lcd_mode:** Should not stay at 0
   - If stuck at 0: LCD not initialized
   - If changing: LCD working, video should appear

---

## Emergency "Minimal Test" Mode

If nothing works, try this minimal test:

**In Control window:**
1. Set batch size to **10000** (small batches)
2. Check RUN
3. Watch main_time increment slowly
4. Check console for errors
5. If main_time increases without errors, increase batch size

This isolates whether the issue is simulation speed vs actual hang.

---

## Report Template

If you need to report the issue, provide:

```
GUI State:
- Responsive? [Yes/No]
- RUN checkbox: [Checked/Unchecked]
- main_time: [Value]
- Is main_time increasing? [Yes/No]

Console Output:
- TEST 3 result: [PASS/FAIL/Not shown]
- Clock divider started, ce_cpu=X: [Value]
- Any errors? [List]

Diagnostics Window:
- ce_cpu edges/1Kcyc: [Value]
- boot_rom_enabled: [0/1]
- main_time: [Value in millions]
- SDRAM reads: [Value]

Task Manager:
- CPU usage: [Percentage]
- Process status: [Running/Not Responding]
```

This information will help identify the exact issue.
