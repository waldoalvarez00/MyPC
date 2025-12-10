# "CPU hitting 7xxx" - What Does This Mean?

**Status:** This is likely **NORMAL BEHAVIOR**, not a bug!

---

## Understanding GameBoy Memory Map

The GameBoy has a 16-bit address bus, allowing access to $0000-$FFFF:

```
$0000-$00FF   Boot ROM (disabled after boot) / Cartridge ROM
$0100-$3FFF   Cartridge ROM Bank 0
$4000-$7FFF   Cartridge ROM Bank N (switchable)
$8000-$9FFF   Video RAM (VRAM)
$A000-$BFFF   Cartridge RAM
$C000-$DFFF   Work RAM (WRAM)
$E000-$FDFF   Echo RAM (mirror of WRAM)
$FE00-$FE9F   Sprite Attribute Table (OAM)
$FF00-$FF7F   I/O Registers
$FF80-$FFFE   High RAM (HRAM)
$FFFF         Interrupt Enable Register
```

---

## What is "CPU Address"?

The `dbg_cpu_addr` signal shows the **ADDRESS BUS**, which is the memory location the CPU is currently accessing. This is **NOT** the Program Counter (PC)!

**Example:**
```
PC = $0150        (CPU executing code at $0150)
cpu_addr = $C005  (CPU reading/writing data at WRAM location $C005)
```

So seeing addresses like $7xxx, $C000, $FF00, etc. is completely normal - it means the CPU is accessing different memory regions while executing code.

---

## Why You See $7xxx Addresses

**$7000-$7FFF** is part of **Cartridge ROM Bank N** (switchable ROM banks).

**Common reasons to see this:**
1. **Reading ROM data:** Game code stored in upper ROM banks
2. **Reading tile data:** Some games store graphics in ROM
3. **Reading lookup tables:** Constants, text strings, etc.

**This is NORMAL!** Most GameBoy games use ROM banks beyond the first 16KB.

---

## What Would Be ABNORMAL

### ❌ Stuck at Same Address
If `cpu_addr` shows the SAME value every cycle:
```
Cycle 1000: cpu_addr = $7123
Cycle 1001: cpu_addr = $7123
Cycle 1002: cpu_addr = $7123  ← STUCK!
```
This indicates the CPU is frozen.

### ❌ Never Leaving Boot ROM Range
If `cpu_addr` is ALWAYS in $0000-$00FF after 5M cycles:
```
Cycle 5000000: cpu_addr = $0042
boot_enabled = 1  ← PROBLEM!
```
This means boot ROM never completed.

### ✅ Varying Addresses (NORMAL)
```
Cycle 1000: cpu_addr = $0150
Cycle 1001: cpu_addr = $C005  (accessing WRAM)
Cycle 1002: cpu_addr = $7ABC  (reading ROM bank)
Cycle 1003: cpu_addr = $FF44  (reading LCD register)
```
This is perfectly normal operation!

---

## How to Check if CPU is Working

### Test 1: Boot ROM Completion

Run the test program in WSL:
```bash
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator
./test_boot_complete
```

**Expected:**
```
✅ Boot ROM DISABLED at cycle 4188552!
```

**If you see:**
```
❌ BOOT ROM NEVER DISABLED!
```
Then there IS a problem.

### Test 2: Address Variety

In the GUI, if you can see debug output, check:
- Does `cpu_addr` change frequently? ✅ Good
- Does it access different ranges ($0xxx, $7xxx, $Cxxx, $FFxx)? ✅ Good
- Is it stuck at one value? ❌ Bad

### Test 3: Boot ROM Status

Check `dbg_boot_rom_enabled`:
- Starts as `1` (enabled) ✅
- Changes to `0` after ~1 second ✅
- Stays `1` forever ❌ Problem

---

## Debug Output Examples

### Normal Execution (After Boot)
```
Time: 1.2s
cpu_addr: $0152      (executing cartridge code)
boot_enabled: 0      (boot ROM disabled)
lcd_mode: 3          (drawing pixels)
lcd_data_gb: 2       (dark gray pixel)
```

### Boot ROM Phase (Normal)
```
Time: 0.5s
cpu_addr: $0042      (executing boot ROM)
boot_enabled: 1      (boot ROM active)
lcd_mode: 0          (HBlank)
lcd_data_gb: 0       (white pixel)
```

### Problem: Stuck in Boot
```
Time: 5.0s
cpu_addr: $0008      (stuck in boot ROM)
boot_enabled: 1      (never disabled!)
lcd_mode: 0
lcd_data_gb: 0       (constant white = problem)
```

---

## What to Look For in GUI

If your GUI shows debug info:

### ✅ GOOD SIGNS
- `boot_enabled` changes from 1 → 0
- `cpu_addr` varies (different values each frame)
- `lcd_data_gb` shows different values (0, 1, 2, 3)
- `lcd_mode` cycles through 0, 1, 2, 3

### ❌ BAD SIGNS
- `boot_enabled` stuck at 1
- `cpu_addr` same value every frame
- `lcd_data_gb` constant (all 0 or all 3)
- Black screen forever

---

## Summary

**"CPU hitting 7xxx"** by itself is **NOT a problem!**

The real questions are:
1. Did boot ROM complete? (`boot_enabled` = 0)
2. Is CPU actually executing? (`cpu_addr` changing)
3. Is display working? (`lcd_data_gb` varying)

**After rebuilding Visual Studio:**
- Boot ROM should complete in ~1 second
- You should see Nintendo logo animation
- Then cartridge graphics should appear

If you STILL see black screen after rebuild, then we have a different problem (likely graphics rendering, not boot ROM).

---

**Action Items:**
1. ✅ Rebuild Visual Studio project (see WINDOWS_REBUILD_INSTRUCTIONS.md)
2. ✅ Run the simulator
3. ✅ Report if boot_enabled changes to 0
4. ✅ Report if you see any graphics
