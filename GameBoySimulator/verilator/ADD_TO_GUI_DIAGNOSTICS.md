# How to Add Diagnostics to Your GUI Simulator

**Status:** FPS showing but black screen = Boot ROM likely completing, VRAM display issue

---

## Quick Diagnostic: Add to Your GUI Code

Find where you're rendering the display in your GUI simulator and add this diagnostic output.

### Location to Add Code

Look for your main rendering loop - probably in a file like:
- `sim.cpp`
- `main.cpp`
- `gameboy_gui.cpp`

Find the section that looks like:
```cpp
while (running) {
    // Simulation tick
    dut->eval();

    // Rendering...
}
```

### Add This Diagnostic Code

**Add BEFORE the rendering loop:**
```cpp
// Add at the top with other variables
static bool boot_rom_completed = false;
static uint64_t frame_count = 0;
static uint64_t boot_complete_frame = 0;
```

**Add INSIDE the main loop:**
```cpp
frame_count++;

// Check if boot ROM completed
if (!boot_rom_completed && dut->dbg_boot_rom_enabled == 0) {
    boot_rom_completed = true;
    boot_complete_frame = frame_count;
    printf("✅ BOOT ROM DISABLED at frame %llu!\n", frame_count);
    printf("   That's about %.2f seconds\n", frame_count / 60.0);
}

// Print status every 60 frames (1 second at 60 FPS)
if (frame_count % 60 == 0) {
    printf("[Frame %6llu] boot=%d addr=$%04X lcd_mode=%d lcd_data=%d\n",
           frame_count,
           dut->dbg_boot_rom_enabled,
           dut->dbg_cpu_addr,
           dut->dbg_lcd_mode,
           dut->dbg_lcd_data_gb);
}
```

### What This Will Show

**If boot ROM completes (GOOD):**
```
[Frame     60] boot=1 addr=$0007 lcd_mode=0 lcd_data=3
✅ BOOT ROM DISABLED at frame 65!
   That's about 1.08 seconds
[Frame    120] boot=0 addr=$0150 lcd_mode=2 lcd_data=3
```

**If boot ROM stuck (BAD):**
```
[Frame     60] boot=1 addr=$0007 lcd_mode=0 lcd_data=3
[Frame    120] boot=1 addr=$0008 lcd_mode=0 lcd_data=3
[Frame    180] boot=1 addr=$0009 lcd_mode=0 lcd_data=3
```

---

## Expected Results

### Scenario 1: Boot ROM Completes, All Black ✅ (Most Likely)

**Console Output:**
```
✅ BOOT ROM DISABLED at frame 65!
[Frame    120] boot=0 addr=$7xxx lcd_mode=2 lcd_data=3
```

**What It Means:**
- ✅ Boot ROM fix WORKED!
- ✅ CPU executing normally (7xxx is ROM access - normal!)
- ❌ lcd_data=3 (black) constantly = VRAM display issue

**Next Step:** Need to fix VRAM initialization/rendering

### Scenario 2: Boot ROM Never Completes ❌

**Console Output:**
```
[Frame    600] boot=1 addr=$0008 lcd_mode=0 lcd_data=3
```

**What It Means:**
- ❌ Build didn't pick up the fix
- Need to delete obj_dir and re-verilate

---

## Alternative: Quick printf in ImGui Window

If you're using ImGui, you can display the info on-screen instead:

```cpp
// In your ImGui rendering code
ImGui::Begin("Debug Info");
ImGui::Text("Boot ROM: %s", dut->dbg_boot_rom_enabled ? "ENABLED" : "DISABLED");
ImGui::Text("CPU Addr: $%04X", dut->dbg_cpu_addr);
ImGui::Text("LCD Mode: %d", dut->dbg_lcd_mode);
ImGui::Text("LCD Data: %d", dut->dbg_lcd_data_gb);
ImGui::End();
```

---

## What to Tell Me

After adding diagnostics, run the simulator and tell me:

1. **Does boot ROM complete?**
   - Do you see "✅ BOOT ROM DISABLED at frame..."?
   - How many seconds does it take?

2. **What are the values after boot?**
   - `boot=?`
   - `addr=$????`
   - `lcd_data=?`

3. **Does lcd_data ever change?**
   - Always 3 (black)?
   - Always 0 (white)?
   - Mixed values?

This will tell us exactly what's wrong!

---

## Current Theory

Based on "FPS showing but all black":

**Most Likely:** Boot ROM completes ✅, but VRAM shows only initialized values (0xFF = black on Windows).

This matches the issue documented in `VRAM_ISSUE_SUMMARY.md`:
- Windows Verilator randomizes VRAM to 0xFF (black)
- Boot ROM writes to VRAM successfully
- But display only shows the randomized values, not the written data

**Next fix:** We need to ensure VRAM writes persist and are read correctly by the LCD controller.
