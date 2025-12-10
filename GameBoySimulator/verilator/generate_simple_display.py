#!/usr/bin/env python3
"""
Generate a minimal GameBoy ROM to test LCD enable.
Just writes 0x91 to LCDC and loops forever (no HALT).
"""

import struct

ROM_SIZE = 32768
ENTRY_POINT = 0x0100
MAIN_CODE = 0x0150

# Nintendo logo (required)
NINTENDO_LOGO = bytes([
    0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
    0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
    0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
    0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
    0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
    0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
])

# Opcodes
NOP = 0x00
JP_nn = 0xC3
JR_n = 0x18
DI = 0xF3
LD_A_n = 0x3E
LDH_an_A = 0xE0

def create_rom():
    rom = bytearray(ROM_SIZE)

    # Entry at 0x0100
    rom[ENTRY_POINT] = NOP
    rom[ENTRY_POINT + 1] = JP_nn
    rom[ENTRY_POINT + 2] = MAIN_CODE & 0xFF
    rom[ENTRY_POINT + 3] = (MAIN_CODE >> 8) & 0xFF

    # Nintendo logo
    for i, b in enumerate(NINTENDO_LOGO):
        rom[0x0104 + i] = b

    # Title
    title = b"SIMPLE LCD TEST"
    for i, b in enumerate(title[:15]):
        rom[0x0134 + i] = b

    # Header
    rom[0x0147] = 0x00  # Cart type
    rom[0x0148] = 0x00  # ROM size
    rom[0x0149] = 0x00  # RAM size

    # Header checksum
    checksum = 0
    for i in range(0x0134, 0x014D):
        checksum = (checksum - rom[i] - 1) & 0xFF
    rom[0x014D] = checksum

    # Also add JP at 0x0000 for boot without boot ROM
    rom[0] = JP_nn
    rom[1] = MAIN_CODE & 0xFF
    rom[2] = (MAIN_CODE >> 8) & 0xFF

    # Main code at 0x0150
    pc = MAIN_CODE

    # DI - Disable interrupts
    rom[pc] = DI
    pc += 1

    # LD A, 0x91 - Load LCD enable value
    rom[pc] = LD_A_n
    pc += 1
    rom[pc] = 0x91  # LCD on, BG on
    pc += 1

    # LDH (0x40), A - Write to LCDC
    rom[pc] = LDH_an_A
    pc += 1
    rom[pc] = 0x40
    pc += 1

    # Infinite loop: JR -2 (jump to itself)
    loop_addr = pc
    rom[pc] = JR_n
    pc += 1
    rom[pc] = 0xFE  # -2 in two's complement
    pc += 1

    print(f"ROM code ends at 0x{pc:04X}")
    print(f"Infinite loop at 0x{loop_addr:04X}")

    return bytes(rom)

def generate_header(rom_data, array_name="simple_lcd_rom"):
    """Generate C header file."""
    lines = [
        "// Auto-generated simple LCD test ROM",
        "#ifndef SIMPLE_LCD_ROM_H",
        "#define SIMPLE_LCD_ROM_H",
        "",
        f"static const unsigned char {array_name}[{len(rom_data)}] = {{",
    ]

    for i in range(0, len(rom_data), 16):
        chunk = rom_data[i:i+16]
        hex_str = ", ".join(f"0x{b:02X}" for b in chunk)
        if i + 16 < len(rom_data):
            hex_str += ","
        lines.append(f"    {hex_str}")

    lines.extend([
        "};",
        "",
        "#endif // SIMPLE_LCD_ROM_H",
        ""
    ])

    return "\n".join(lines)

def main():
    print("Generating simple LCD test ROM...")

    rom_data = create_rom()

    # Write binary
    with open("simple_lcd.gb", "wb") as f:
        f.write(rom_data)
    print("Written: simple_lcd.gb")

    # Write header
    header = generate_header(rom_data)
    with open("simple_lcd_rom.h", "w") as f:
        f.write(header)
    print("Written: simple_lcd_rom.h")

    print("\nROM contents:")
    print(f"  0x0000: {rom_data[0]:02X} {rom_data[1]:02X} {rom_data[2]:02X}  JP 0x{rom_data[1] | (rom_data[2] << 8):04X}")
    print(f"  0x0150: {rom_data[0x150]:02X}        DI")
    print(f"  0x0151: {rom_data[0x151]:02X} {rom_data[0x152]:02X}     LD A, 0x{rom_data[0x152]:02X}")
    print(f"  0x0153: {rom_data[0x153]:02X} {rom_data[0x154]:02X}     LDH (0x{rom_data[0x154]:02X}), A")
    print(f"  0x0155: {rom_data[0x155]:02X} {rom_data[0x156]:02X}     JR 0x{rom_data[0x156]:02X}")

if __name__ == "__main__":
    main()
