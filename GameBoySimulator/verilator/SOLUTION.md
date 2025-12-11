# GameBoy Simulator - Interrupt Storm Solution

## Root Cause Discovered

The issue is **NOT an interrupt storm**. The real problem is:

**The JP $0100 instruction straddles the boot ROM disable boundary.**

### What Happens:

1. Boot ROM executes: `LDH ($FF50), A` - This disables the boot ROM
2. Next instruction is: `JP $0100` (3 bytes: 0xC3 0x00 0x01)
3. CPU fetches opcode 0xC3 from boot ROM (address 0x0D)
4. **Boot ROM disables (boot_rom_enabled = 0)**
5. CPU tries to fetch operand bytes (0x00 0x01) from addresses 0x0E, 0x0F
6. **But boot ROM is now disabled, so it reads from CART ROM instead!**
7. Cart ROM at 0x0E, 0x0F contains 0xFF 0xFF (uninitialized)
8. JP decodes as `JP $FFFF` instead of `JP $0100`
9. PC goes to 0xFFFF → wraps to 0xFFFD
10. Eventually jumps to 0x0038 (RST $38)

## Solution

**Option 1: Move JP BEFORE Boot ROM Disable**

Put the target address in a register, disable boot ROM, then jump via register:

```assembly
; Instead of:
LDH ($FF50), A    ; Disable boot ROM
JP $0100          ; Jump to cart (WRONG - reads from cart ROM!)

; Do this:
LD HL, $0100      ; Load target address into HL
LDH ($FF50), A    ; Disable boot ROM
JP (HL)           ; Jump via register (reads from register, not memory)
```

**Option 2: Reverse the Order**

Jump to cart FIRST, let cart code disable boot ROM:

```assembly
; Boot ROM:
JP $0100          ; Jump to cart (reads all 3 bytes from boot ROM)

; Cart ROM at 0x0100:
LD A, $01
LDH ($FF50), A    ; Cart disables boot ROM
; ... rest of cart code
```

**Option 3: Use Real DMG Boot ROM with Zero Latency**

The real DMG boot ROM might be designed to work with zero-latency memory. Try:
```cpp
sdram->cas_latency = 0;  // Use zero-latency for boot ROM compatibility
```

## Recommended Fix for sim_main_gui.cpp

Update the minimal boot ROM to use Option 1 (JP via register):

```cpp
// Around line 1130 in sim_main_gui.cpp:
int pc = 0;

// 0. Disable interrupts
minimal_boot[pc++] = 0xF3;  // DI

// 1. Turn off LCD
minimal_boot[pc++] = 0x3E;  // LD A, $00
minimal_boot[pc++] = 0x00;
minimal_boot[pc++] = 0xE0;  // LDH ($FF40), A  ; LCDC = 0
minimal_boot[pc++] = 0x40;

// ... (other initialization code) ...

// CRITICAL FIX: Load jump target into register BEFORE disabling boot ROM
minimal_boot[pc++] = 0x21;  // LD HL, $0100
minimal_boot[pc++] = 0x00;
minimal_boot[pc++] = 0x01;

// Now disable boot ROM
minimal_boot[pc++] = 0x3E;  // LD A, $01
minimal_boot[pc++] = 0x01;
minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A  ; Disable boot ROM
minimal_boot[pc++] = 0x50;

// Jump via register (safe - doesn't read from memory)
minimal_boot[pc++] = 0xE9;  // JP (HL)
```

## Why This Works

### Original (BROKEN):
```
Address  Boot ROM       Action
-------  -------------  ------
0x0D     0xC3           CPU fetches opcode (JP)
0x0E     0x00           Boot ROM disabled! Cart ROM returns 0xFF
0x0F     0x01           Boot ROM disabled! Cart ROM returns 0xFF
         → JP $FFFF     WRONG ADDRESS!
```

### Fixed (WORKING):
```
Address  Boot ROM       Action
-------  -------------  ------
0x0D     0x21           LD HL, $0100 (all 3 bytes from boot ROM)
0x0E     0x00
0x0F     0x01
0x10     0x3E           LD A, $01 (all 2 bytes from boot ROM)
0x11     0x01
0x12     0xE0           LDH ($FF50), A (all 2 bytes from boot ROM)
0x13     0x50           Boot ROM disables HERE
0x14     0xE9           JP (HL) - only 1 byte, reads from boot ROM
                        Jump target already in HL register!
         → JP to 0x0100  CORRECT!
```

## Additional Changes

### 1. Revert sim_main_gui.cpp Line 1106
```cpp
// REVERT THIS (uncomment loadBootROM):
// loadBootROM();  // DISABLED: Real DMG boot ROM gets stuck

// BACK TO:
loadBootROM();  // Load real DMG boot ROM if available
```

### 2. Fix Real DMG Boot ROM (if used)
The real DMG boot ROM likely also needs fixing, OR it was designed for zero-latency memory.

**Option A**: Use zero-latency for boot ROM only:
```cpp
// In sim_main_gui.cpp init:
sdram->cas_latency = 0;  // Zero latency for boot ROM
// ... boot ROM executes ...
sdram->cas_latency = 2;  // Switch to realistic latency for cart ROM
```

**Option B**: Use minimal boot ROM always (current approach):
```cpp
// Keep loadBootROM() commented out
// loadBootROM();  // Real DMG boot ROM has timing issues with realistic latency
```

## Testing the Fix

Create a test to verify the fix:

```cpp
// test_fixed_boot_rom.cpp
uint8_t minimal_boot[256];
memset(minimal_boot, 0, 256);

int pc = 0;
minimal_boot[pc++] = 0xF3;  // DI

// Load jump target into HL BEFORE disabling boot ROM
minimal_boot[pc++] = 0x21;  // LD HL, $0100
minimal_boot[pc++] = 0x00;
minimal_boot[pc++] = 0x01;

// Disable boot ROM
minimal_boot[pc++] = 0x3E;  // LD A, $01
minimal_boot[pc++] = 0x01;
minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
minimal_boot[pc++] = 0x50;

// Jump via register
minimal_boot[pc++] = 0xE9;  // JP (HL)

// Upload and test...
// Expected: PC goes to 0x0100, NOT 0xFFFD
```

## Status

✅ **ROOT CAUSE IDENTIFIED**
✅ **SOLUTION DESIGNED**
⏳ **IMPLEMENTATION PENDING**

The "interrupt storm" was actually a boot ROM transition bug caused by the JP instruction reading operands from the wrong memory region after boot ROM disable.

---

*Solution Date: 2025-12-11*
*Root Cause: JP instruction straddles boot ROM disable boundary*
*Fix: Use `JP (HL)` instead of `JP $0100`*
