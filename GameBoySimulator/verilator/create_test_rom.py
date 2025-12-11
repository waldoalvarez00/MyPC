#!/usr/bin/env python3
"""
Create a minimal test GameBoy ROM for debugging boot ROM transition.
This ROM has proper interrupt handlers and simple test code.
"""

# Create 32KB ROM (minimum size)
rom = bytearray(32768)

# Fill with HALT (0x76) to make errors obvious
for i in range(len(rom)):
    rom[i] = 0x76  # HALT

# Interrupt vectors with RETI
rom[0x40] = 0xD9  # VBlank: RETI
rom[0x48] = 0xD9  # LCD STAT: RETI
rom[0x50] = 0xD9  # Timer: RETI
rom[0x58] = 0xD9  # Serial: RETI
rom[0x60] = 0xD9  # Joypad: RETI

# Entry point at 0x0100
rom[0x100] = 0x00  # NOP
rom[0x101] = 0xC3  # JP $0150
rom[0x102] = 0x50
rom[0x103] = 0x01

# Nintendo logo (required for boot ROM logo check)
logo = bytes([
    0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
    0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
    0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
    0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
    0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
    0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
])
rom[0x104:0x104+len(logo)] = logo

# Title
title = b"TEST ROM"
rom[0x134:0x134+len(title)] = title

# Cart type: ROM ONLY (0x00)
rom[0x147] = 0x00

# ROM size: 32KB (code 0x00)
rom[0x148] = 0x00

# RAM size: None (code 0x00)
rom[0x149] = 0x00

# Header checksum (simple calculation)
checksum = 0
for addr in range(0x134, 0x14D):
    checksum = checksum - rom[addr] - 1
checksum = checksum & 0xFF
rom[0x14D] = checksum

# Main program at 0x0150
pc = 0x150

# 0. Disable interrupts
rom[pc] = 0xF3  # DI
pc += 1

# 1. Set stack pointer
rom[pc] = 0x31  # LD SP, $FFFE
pc += 1
rom[pc] = 0xFE
pc += 1
rom[pc] = 0xFF
pc += 1

# 2. Clear interrupt enable register (no interrupts)
rom[pc] = 0x3E  # LD A, $00
pc += 1
rom[pc] = 0x00
pc += 1
rom[pc] = 0xE0  # LDH ($FFFF), A
pc += 1
rom[pc] = 0xFF
pc += 1

# 3. Turn off LCD (prevent VBlank interrupts)
rom[pc] = 0x3E  # LD A, $00
pc += 1
rom[pc] = 0x00
pc += 1
rom[pc] = 0xE0  # LDH ($FF40), A
pc += 1
rom[pc] = 0x40
pc += 1

# 4. Infinite loop
rom[pc] = 0x00  # NOP
pc += 1
loop_start = pc
rom[pc] = 0x18  # JR -2 (loop forever)
pc += 1
rom[pc] = 0xFD  # -3 in two's complement
pc += 1

print(f"Test ROM created: {len(rom)} bytes")
print(f"  Entry point: 0x0100 -> JP $0150")
print(f"  Main program: 0x0150 (DI, set SP, clear IE, turn off LCD, loop)")
print(f"  Interrupt handlers: RETI at 0x40, 0x48, 0x50, 0x58, 0x60")
print(f"  Cart type: ROM ONLY")
print(f"  ROM size: 32KB")
print(f"  Header checksum: 0x{checksum:02X}")

# Write to file
with open("test_boot_transition.gb", "wb") as f:
    f.write(rom)

print("\nSaved to: test_boot_transition.gb")
print("\nTo test:")
print("  1. Copy test_boot_transition.gb to GameBoySimulator/verilator/")
print("  2. Rename to game.gb (or specify in simulator)")
print("  3. Run simulator")
print("  4. Expected: PC stays in loop at 0x015A-0x015B, no crash")
