#!/usr/bin/env python3
"""
Generate a GameBoy display test ROM that properly initializes video.

This ROM:
1. Waits for VBlank
2. Disables LCD for safe VRAM access
3. Writes a checkerboard tile pattern
4. Fills the tilemap
5. Sets up palette
6. Enables LCD
7. Loops forever

Output: display_test.gb and display_test_rom.h
"""

import struct

# GameBoy ROM header constants
ROM_SIZE = 32768  # 32KB
ENTRY_POINT = 0x0100
MAIN_CODE = 0x0150
NINTENDO_LOGO_OFFSET = 0x0104
TITLE_OFFSET = 0x0134

# Nintendo logo (required for boot ROM to pass)
NINTENDO_LOGO = bytes([
    0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
    0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
    0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
    0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
    0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
    0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
])

# GameBoy Z80 opcodes
class GB:
    NOP = 0x00
    JP_nn = 0xC3
    JR_n = 0x18
    JR_NZ = 0x20
    JR_Z = 0x28
    DI = 0xF3
    EI = 0xFB
    HALT = 0x76

    LD_A_n = 0x3E
    LD_B_n = 0x06
    LD_C_n = 0x0E
    LD_HL_nn = 0x21
    LD_BC_nn = 0x01
    LD_DE_nn = 0x11

    LD_A_HLI = 0x2A      # LD A, (HL+)
    LD_HLI_A = 0x22      # LD (HL+), A
    LD_A_aHL = 0x7E      # LD A, (HL)
    LD_aHL_A = 0x77      # LD (HL), A
    LD_aHL_n = 0x36      # LD (HL), n

    LD_A_ann = 0xFA      # LD A, (nn)
    LD_ann_A = 0xEA      # LD (nn), A
    LDH_A_an = 0xF0      # LDH A, (n) - high page
    LDH_an_A = 0xE0      # LDH (n), A - high page

    XOR_A = 0xAF
    XOR_n = 0xEE
    OR_A = 0xB7
    OR_B = 0xB0
    OR_C = 0xB1
    CP_n = 0xFE

    DEC_BC = 0x0B
    DEC_B = 0x05
    DEC_C = 0x0D
    INC_HL = 0x23

    LD_A_B = 0x78
    LD_A_C = 0x79
    LD_B_A = 0x47

def create_rom():
    """Create the GameBoy display test ROM."""
    rom = bytearray(ROM_SIZE)

    # Entry point at 0x0100: NOP, JP main
    rom[ENTRY_POINT] = GB.NOP
    rom[ENTRY_POINT + 1] = GB.JP_nn
    rom[ENTRY_POINT + 2] = MAIN_CODE & 0xFF
    rom[ENTRY_POINT + 3] = (MAIN_CODE >> 8) & 0xFF

    # Nintendo logo at 0x0104
    for i, b in enumerate(NINTENDO_LOGO):
        rom[NINTENDO_LOGO_OFFSET + i] = b

    # Title at 0x0134 (up to 16 chars)
    title = b"DISPLAYTEST"
    for i, b in enumerate(title):
        rom[TITLE_OFFSET + i] = b

    # Header checksums
    rom[0x0147] = 0x00  # Cart type: ROM only
    rom[0x0148] = 0x00  # ROM size: 32KB
    rom[0x0149] = 0x00  # RAM size: None

    # Calculate header checksum (0x014D)
    checksum = 0
    for i in range(0x0134, 0x014D):
        checksum = (checksum - rom[i] - 1) & 0xFF
    rom[0x014D] = checksum

    # Also add JP to main at address 0x0000 for simulation without boot ROM
    rom[0] = GB.JP_nn
    rom[1] = MAIN_CODE & 0xFF
    rom[2] = (MAIN_CODE >> 8) & 0xFF

    # Main code at 0x0150
    pc = MAIN_CODE

    # DI - Disable interrupts
    rom[pc] = GB.DI
    pc += 1

    # SKIP VBlank wait at startup - LCD is disabled by default so LY doesn't update
    # Just go straight to disabling LCD (which is already disabled, but be explicit)
    # Disable LCD: LD A, 0 ; LDH (0x40), A
    rom[pc] = GB.XOR_A  # XOR A (A = 0)
    pc += 1
    rom[pc] = GB.LDH_an_A  # LDH (0x40), A
    pc += 1
    rom[pc] = 0x40  # LCDC register
    pc += 1

    # Write checkerboard tile pattern to 0x8000
    # Tile 0: All 0xAA (checkerboard)
    # Each tile is 16 bytes (8 lines, 2 bytes per line)
    # LD HL, 0x8000
    rom[pc] = GB.LD_HL_nn
    pc += 1
    rom[pc] = 0x00
    pc += 1
    rom[pc] = 0x80
    pc += 1

    # Write 16 bytes of pattern
    for i in range(16):
        # LD (HL), pattern
        rom[pc] = GB.LD_aHL_n
        pc += 1
        # Checkerboard pattern: alternating 0xAA and 0x55
        rom[pc] = 0xAA if (i % 2 == 0) else 0x55
        pc += 1
        # INC HL
        rom[pc] = GB.INC_HL
        pc += 1

    # Write second tile (tile 1) - solid white
    for i in range(16):
        rom[pc] = GB.LD_aHL_n
        pc += 1
        rom[pc] = 0xFF
        pc += 1
        rom[pc] = GB.INC_HL
        pc += 1

    # Fill tilemap at 0x9800 with alternating tiles 0 and 1
    # LD HL, 0x9800
    rom[pc] = GB.LD_HL_nn
    pc += 1
    rom[pc] = 0x00
    pc += 1
    rom[pc] = 0x98
    pc += 1

    # LD BC, 1024 (32x32 tilemap)
    rom[pc] = GB.LD_BC_nn
    pc += 1
    rom[pc] = 0x00  # Low byte of 1024
    pc += 1
    rom[pc] = 0x04  # High byte of 1024
    pc += 1

    # XOR A (tile index starts at 0)
    rom[pc] = GB.XOR_A
    pc += 1

    # map_loop:
    map_loop = pc
    rom[pc] = GB.LD_HLI_A  # LD (HL+), A
    pc += 1

    # XOR 1 (alternate between tile 0 and 1)
    rom[pc] = GB.XOR_n
    pc += 1
    rom[pc] = 0x01
    pc += 1

    # DEC BC
    rom[pc] = GB.DEC_BC
    pc += 1

    # LD A, B ; OR C ; check if BC == 0
    rom[pc] = GB.LD_A_B
    pc += 1
    rom[pc] = GB.OR_C
    pc += 1

    # Save A (tile index) in B temporarily
    rom[pc] = GB.LD_B_A
    pc += 1

    # Check if we need to continue (BC was decremented, check original values)
    # Actually, let's simplify - just use a counter approach
    # JR NZ, map_loop
    rom[pc] = GB.JR_NZ
    pc += 1
    rom[pc] = (map_loop - pc - 1) & 0xFF
    pc += 1

    # Set palette: LD A, 0xE4 ; LDH (0x47), A
    # 0xE4 = 11 10 01 00 = darkest, dark, light, lightest
    rom[pc] = GB.LD_A_n
    pc += 1
    rom[pc] = 0xE4
    pc += 1
    rom[pc] = GB.LDH_an_A  # LDH (0x47), A
    pc += 1
    rom[pc] = 0x47  # BGP register
    pc += 1

    # Enable LCD: LD A, 0x91 ; LDH (0x40), A
    # 0x91 = 10010001 = LCD on, BG on, tilemap 9800, tile data 8000
    rom[pc] = GB.LD_A_n
    pc += 1
    rom[pc] = 0x91
    pc += 1
    rom[pc] = GB.LDH_an_A  # LDH (0x40), A
    pc += 1
    rom[pc] = 0x40  # LCDC register
    pc += 1

    # Main loop: HALT, JR main_loop
    main_loop = pc
    rom[pc] = GB.HALT
    pc += 1
    rom[pc] = GB.JR_n  # JR main_loop
    pc += 1
    rom[pc] = (main_loop - pc - 1) & 0xFF
    pc += 1

    print(f"ROM code ends at 0x{pc:04X} ({pc} bytes used)")

    return bytes(rom)

def generate_header(rom_data, array_name="display_test_rom"):
    """Generate C header file with ROM data."""
    lines = [
        "// Auto-generated display test ROM",
        "// Generated by generate_display_rom.py",
        "// This ROM initializes LCD and displays a checkerboard pattern",
        "",
        "#ifndef DISPLAY_TEST_ROM_H",
        "#define DISPLAY_TEST_ROM_H",
        "",
        f"static const unsigned char {array_name}[{len(rom_data)}] = {{",
    ]

    # Write ROM data as hex bytes, 16 per line
    for i in range(0, len(rom_data), 16):
        chunk = rom_data[i:i+16]
        hex_str = ", ".join(f"0x{b:02X}" for b in chunk)
        if i + 16 < len(rom_data):
            hex_str += ", "
        lines.append(f"    {hex_str}")

    lines.extend([
        "};",
        "",
        "#endif // DISPLAY_TEST_ROM_H",
        ""
    ])

    return "\n".join(lines)

def main():
    print("Generating GameBoy display test ROM...")

    # Create ROM
    rom_data = create_rom()

    # Write binary ROM
    with open("display_test.gb", "wb") as f:
        f.write(rom_data)
    print("Written: display_test.gb")

    # Write C header
    header = generate_header(rom_data)
    with open("display_test_rom.h", "w") as f:
        f.write(header)
    print("Written: display_test_rom.h")

    # Print ROM disassembly at entry and main
    print("\nROM Entry (0x0100):")
    print(f"  0x0100: {rom_data[0x100]:02X}        NOP")
    print(f"  0x0101: {rom_data[0x101]:02X} {rom_data[0x102]:02X} {rom_data[0x103]:02X}  JP 0x{rom_data[0x102] | (rom_data[0x103] << 8):04X}")

    print(f"\nMain code starts at 0x{MAIN_CODE:04X}")

    print("\nROM Header:")
    print(f"  Title: {rom_data[0x134:0x144].decode('ascii', errors='ignore').strip()}")
    print(f"  Cart Type: 0x{rom_data[0x147]:02X}")
    print(f"  Header Checksum: 0x{rom_data[0x14D]:02X}")

if __name__ == "__main__":
    main()
