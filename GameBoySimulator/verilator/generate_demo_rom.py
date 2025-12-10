#!/usr/bin/env python3
"""
GameBoy Built-in Demo ROM Generator
Generates a valid GB ROM that displays "NO CARTRIDGE" with animation
"""

import struct

# Nintendo logo (required for boot ROM validation)
NINTENDO_LOGO = bytes([
    0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
    0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
    0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
    0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
    0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
    0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
])

# Simple 8x8 font for characters (A-Z, 0-9, space, and some symbols)
# Each character is 8 bytes (1 bit per pixel, 8 rows)
FONT_DATA = {
    ' ': [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    'A': [0x18, 0x3C, 0x66, 0x7E, 0x66, 0x66, 0x66, 0x00],
    'B': [0x7C, 0x66, 0x7C, 0x66, 0x66, 0x66, 0x7C, 0x00],
    'C': [0x3C, 0x66, 0x60, 0x60, 0x60, 0x66, 0x3C, 0x00],
    'D': [0x78, 0x6C, 0x66, 0x66, 0x66, 0x6C, 0x78, 0x00],
    'E': [0x7E, 0x60, 0x7C, 0x60, 0x60, 0x60, 0x7E, 0x00],
    'F': [0x7E, 0x60, 0x7C, 0x60, 0x60, 0x60, 0x60, 0x00],
    'G': [0x3C, 0x66, 0x60, 0x6E, 0x66, 0x66, 0x3C, 0x00],
    'H': [0x66, 0x66, 0x7E, 0x66, 0x66, 0x66, 0x66, 0x00],
    'I': [0x3C, 0x18, 0x18, 0x18, 0x18, 0x18, 0x3C, 0x00],
    'J': [0x1E, 0x0C, 0x0C, 0x0C, 0x6C, 0x6C, 0x38, 0x00],
    'K': [0x66, 0x6C, 0x78, 0x70, 0x78, 0x6C, 0x66, 0x00],
    'L': [0x60, 0x60, 0x60, 0x60, 0x60, 0x60, 0x7E, 0x00],
    'M': [0x63, 0x77, 0x7F, 0x6B, 0x63, 0x63, 0x63, 0x00],
    'N': [0x66, 0x76, 0x7E, 0x7E, 0x6E, 0x66, 0x66, 0x00],
    'O': [0x3C, 0x66, 0x66, 0x66, 0x66, 0x66, 0x3C, 0x00],
    'P': [0x7C, 0x66, 0x66, 0x7C, 0x60, 0x60, 0x60, 0x00],
    'Q': [0x3C, 0x66, 0x66, 0x66, 0x66, 0x3C, 0x0E, 0x00],
    'R': [0x7C, 0x66, 0x66, 0x7C, 0x78, 0x6C, 0x66, 0x00],
    'S': [0x3C, 0x66, 0x60, 0x3C, 0x06, 0x66, 0x3C, 0x00],
    'T': [0x7E, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x00],
    'U': [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x3C, 0x00],
    'V': [0x66, 0x66, 0x66, 0x66, 0x66, 0x3C, 0x18, 0x00],
    'W': [0x63, 0x63, 0x63, 0x6B, 0x7F, 0x77, 0x63, 0x00],
    'X': [0x66, 0x66, 0x3C, 0x18, 0x3C, 0x66, 0x66, 0x00],
    'Y': [0x66, 0x66, 0x66, 0x3C, 0x18, 0x18, 0x18, 0x00],
    'Z': [0x7E, 0x06, 0x0C, 0x18, 0x30, 0x60, 0x7E, 0x00],
    '0': [0x3C, 0x66, 0x6E, 0x76, 0x66, 0x66, 0x3C, 0x00],
    '1': [0x18, 0x38, 0x18, 0x18, 0x18, 0x18, 0x7E, 0x00],
    '2': [0x3C, 0x66, 0x06, 0x1C, 0x30, 0x60, 0x7E, 0x00],
    '3': [0x3C, 0x66, 0x06, 0x1C, 0x06, 0x66, 0x3C, 0x00],
    '4': [0x0C, 0x1C, 0x3C, 0x6C, 0x7E, 0x0C, 0x0C, 0x00],
    '5': [0x7E, 0x60, 0x7C, 0x06, 0x06, 0x66, 0x3C, 0x00],
    '6': [0x3C, 0x60, 0x60, 0x7C, 0x66, 0x66, 0x3C, 0x00],
    '7': [0x7E, 0x06, 0x0C, 0x18, 0x30, 0x30, 0x30, 0x00],
    '8': [0x3C, 0x66, 0x66, 0x3C, 0x66, 0x66, 0x3C, 0x00],
    '9': [0x3C, 0x66, 0x66, 0x3E, 0x06, 0x06, 0x3C, 0x00],
    '-': [0x00, 0x00, 0x00, 0x7E, 0x00, 0x00, 0x00, 0x00],
    '.': [0x00, 0x00, 0x00, 0x00, 0x00, 0x18, 0x18, 0x00],
    '!': [0x18, 0x18, 0x18, 0x18, 0x00, 0x00, 0x18, 0x00],
    ':': [0x00, 0x18, 0x18, 0x00, 0x18, 0x18, 0x00, 0x00],
}

def create_tile(char_data):
    """Convert 1bpp font data to GameBoy 2bpp tile format"""
    tile = []
    for row in char_data:
        # GameBoy tiles: low byte then high byte for each row
        # For simple black on white: low=data, high=data (color 3)
        tile.append(row)  # Low byte
        tile.append(row)  # High byte (same = color 3 where set)
    return bytes(tile)

def assemble_code():
    """Generate the demo ROM code"""
    code = bytearray()

    # Constants
    LCDC = 0xFF40
    STAT = 0xFF41
    SCY = 0xFF42
    SCX = 0xFF43
    LY = 0xFF44
    BGP = 0xFF47
    OBP0 = 0xFF48
    OBP1 = 0xFF49
    NR52 = 0xFF26  # Sound on/off
    NR50 = 0xFF24  # Channel control
    NR51 = 0xFF25  # Sound panning
    NR10 = 0xFF10  # Channel 1 sweep
    NR11 = 0xFF11  # Channel 1 length/duty
    NR12 = 0xFF12  # Channel 1 envelope
    NR13 = 0xFF13  # Channel 1 freq low
    NR14 = 0xFF14  # Channel 1 freq high + trigger
    JOYP = 0xFF00

    # Helper to add instructions
    def add(*bytes_):
        code.extend(bytes_)

    # ===== Entry point at 0x0150 =====

    # DI - disable interrupts
    add(0xF3)

    # LD SP, 0xFFFE - set stack pointer
    add(0x31, 0xFE, 0xFF)

    # === Wait for VBlank before touching VRAM ===
    # wait_vblank_1:
    #   LD A, (0xFF44)
    #   CP 144
    #   JR C, wait_vblank_1
    add(0xF0, 0x44)      # LDH A, (LY)
    add(0xFE, 144)       # CP 144
    add(0x38, 0xFA)      # JR C, -6 (back to LDH)

    # === Turn off LCD ===
    # XOR A
    # LD (0xFF40), A
    add(0xAF)            # XOR A
    add(0xE0, 0x40)      # LDH (LCDC), A

    # === Copy font tiles to VRAM ===
    # LD HL, 0x8000 (tile data area)
    # LD DE, font_data
    # LD BC, font_length
    # copy_loop:
    #   LD A, (DE)
    #   LD (HL+), A
    #   INC DE
    #   DEC BC
    #   LD A, B
    #   OR C
    #   JR NZ, copy_loop

    add(0x21, 0x00, 0x80)  # LD HL, 0x8000
    add(0x11, 0x00, 0x02)  # LD DE, 0x0200 (font data location in ROM)
    add(0x01, 0x00, 0x04)  # LD BC, 0x0400 (32 tiles * 16 bytes * 2)

    # copy_loop: (offset = current position)
    copy_loop_start = len(code)
    add(0x1A)              # LD A, (DE)
    add(0x22)              # LD (HL+), A
    add(0x13)              # INC DE
    add(0x0B)              # DEC BC
    add(0x78)              # LD A, B
    add(0xB1)              # OR C
    add(0x20, 0xF8)        # JR NZ, copy_loop (-8)

    # === Clear tilemap ===
    # LD HL, 0x9800
    # LD A, 0 (space tile)
    # LD BC, 0x0400
    add(0x21, 0x00, 0x98)  # LD HL, 0x9800
    add(0x3E, 0x00)        # LD A, 0 (space)
    add(0x01, 0x00, 0x04)  # LD BC, 0x0400

    # clear_loop:
    add(0x22)              # LD (HL+), A
    add(0x0B)              # DEC BC
    add(0x78)              # LD A, B
    add(0xB1)              # OR C
    add(0x20, 0xFA)        # JR NZ, clear_loop (-6)

    # === Write "NO CARTRIDGE" to tilemap ===
    # Text at row 8 (center-ish), starting at column 4
    # Tilemap row 8 = 0x9800 + 8*32 = 0x9900

    # LD HL, 0x9900 + 2 (row 8, col 2)
    add(0x21, 0x02, 0x99)  # LD HL, 0x9902

    # Write "NO CARTRIDGE" - tile indices match character order in font
    # N=14, O=15, space=0, C=3, A=1, R=18, T=20, R=18, I=9, D=4, G=7, E=5
    text = "NO CARTRIDGE"
    for char in text:
        if char == ' ':
            tile_idx = 0
        elif char >= 'A' and char <= 'Z':
            tile_idx = ord(char) - ord('A') + 1
        else:
            tile_idx = 0
        add(0x36, tile_idx)  # LD (HL), tile_idx
        add(0x23)            # INC HL

    # === Write "INSERT GAME" below ===
    # LD HL, 0x9920 + 3 (row 9, col 3)
    add(0x21, 0x23, 0x99)  # LD HL, 0x9923

    text2 = "INSERT GAME"
    for char in text2:
        if char == ' ':
            tile_idx = 0
        elif char >= 'A' and char <= 'Z':
            tile_idx = ord(char) - ord('A') + 1
        else:
            tile_idx = 0
        add(0x36, tile_idx)  # LD (HL), tile_idx
        add(0x23)            # INC HL

    # === Write "PRESS START" below ===
    add(0x21, 0x63, 0x99)  # LD HL, 0x9963 (row 11, col 3)

    text3 = "PRESS START"
    for char in text3:
        if char == ' ':
            tile_idx = 0
        elif char >= 'A' and char <= 'Z':
            tile_idx = ord(char) - ord('A') + 1
        else:
            tile_idx = 0
        add(0x36, tile_idx)  # LD (HL), tile_idx
        add(0x23)            # INC HL

    # === Initialize sound ===
    # LD A, 0x80
    # LD (NR52), A  ; Enable sound
    add(0x3E, 0x80)        # LD A, 0x80
    add(0xE0, 0x26)        # LDH (NR52), A

    # LD A, 0x77
    # LD (NR50), A  ; Max volume both channels
    add(0x3E, 0x77)        # LD A, 0x77
    add(0xE0, 0x24)        # LDH (NR50), A

    # LD A, 0x11
    # LD (NR51), A  ; Channel 1 to both outputs
    add(0x3E, 0x11)        # LD A, 0x11
    add(0xE0, 0x25)        # LDH (NR51), A

    # === Set palette (black on white) ===
    # BGP = 0xE4 = 11 10 01 00 = black, dark, light, white
    add(0x3E, 0xE4)        # LD A, 0xE4
    add(0xE0, 0x47)        # LDH (BGP), A

    # === Turn on LCD ===
    # LCDC = 0x91 = LCD on, BG on, BG tile data at 0x8000
    add(0x3E, 0x91)        # LD A, 0x91
    add(0xE0, 0x40)        # LDH (LCDC), A

    # === Main loop ===
    # Animate scroll and check buttons

    # Initialize scroll counter in B
    add(0x06, 0x00)        # LD B, 0 (scroll animation counter)
    add(0x0E, 0x00)        # LD C, 0 (frame counter)

    # main_loop:
    main_loop_pos = len(code)

    # Wait for VBlank
    add(0xF0, 0x44)        # LDH A, (LY)
    add(0xFE, 144)         # CP 144
    add(0x20, 0xFA)        # JR NZ, -6 (wait)

    # Update scroll Y for wave effect
    add(0x78)              # LD A, B
    add(0xE6, 0x07)        # AND 0x07 (only use low 3 bits)
    add(0xE0, 0x42)        # LDH (SCY), A

    # Increment animation counter
    add(0x0C)              # INC C
    add(0x79)              # LD A, C
    add(0xE6, 0x07)        # AND 0x07
    add(0x20, 0x01)        # JR NZ, skip_inc_b
    add(0x04)              # INC B
    # skip_inc_b:

    # === Cycle palette colors every 64 frames ===
    add(0x79)              # LD A, C
    add(0xE6, 0x3F)        # AND 0x3F
    add(0x20, 0x09)        # JR NZ, skip_palette

    # Rotate palette
    add(0xF0, 0x47)        # LDH A, (BGP)
    add(0x07)              # RLCA
    add(0x07)              # RLCA
    add(0xE0, 0x47)        # LDH (BGP), A
    # skip_palette:

    # === Check joypad ===
    # Select buttons (not d-pad)
    add(0x3E, 0x20)        # LD A, 0x20
    add(0xE0, 0x00)        # LDH (JOYP), A

    # Read a few times for debounce
    add(0xF0, 0x00)        # LDH A, (JOYP)
    add(0xF0, 0x00)        # LDH A, (JOYP)

    # Check if any button pressed (bits 0-3 go low)
    add(0xE6, 0x0F)        # AND 0x0F
    add(0xFE, 0x0F)        # CP 0x0F (no buttons = 0x0F)
    add(0x28, 0x12)        # JR Z, no_button (skip sound)

    # === Play beep on button press ===
    add(0x3E, 0x00)        # LD A, 0x00
    add(0xE0, 0x10)        # LDH (NR10), A  ; No sweep

    add(0x3E, 0x80)        # LD A, 0x80
    add(0xE0, 0x11)        # LDH (NR11), A  ; 50% duty

    add(0x3E, 0xF3)        # LD A, 0xF3
    add(0xE0, 0x12)        # LDH (NR12), A  ; Envelope: vol 15, decrease

    add(0x3E, 0x83)        # LD A, 0x83
    add(0xE0, 0x13)        # LDH (NR13), A  ; Freq low

    add(0x3E, 0x87)        # LD A, 0x87
    add(0xE0, 0x14)        # LDH (NR14), A  ; Freq high + trigger

    # no_button:

    # Wait for VBlank to end
    add(0xF0, 0x44)        # LDH A, (LY)
    add(0xFE, 144)         # CP 144
    add(0x30, 0xFA)        # JR NC, -6 (wait while >= 144)

    # Jump back to main_loop
    # Calculate relative jump
    jump_back = main_loop_pos - len(code) - 2
    add(0x18, jump_back & 0xFF)  # JR main_loop

    return bytes(code)

def generate_font_tiles():
    """Generate all font tiles in order"""
    tiles = bytearray()

    # Tile 0 = space
    tiles.extend(create_tile(FONT_DATA[' ']))

    # Tiles 1-26 = A-Z
    for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
        if c in FONT_DATA:
            tiles.extend(create_tile(FONT_DATA[c]))
        else:
            tiles.extend(create_tile(FONT_DATA[' ']))

    # Tiles 27-36 = 0-9
    for c in '0123456789':
        if c in FONT_DATA:
            tiles.extend(create_tile(FONT_DATA[c]))
        else:
            tiles.extend(create_tile(FONT_DATA[' ']))

    # Pad to expected size
    while len(tiles) < 0x400:
        tiles.extend([0x00] * 16)

    return bytes(tiles)

def generate_demo_rom():
    """Generate the complete demo ROM"""
    rom = bytearray(32768)  # 32KB ROM

    # Entry point at 0x0100: JP 0x0150
    rom[0x100] = 0xC3  # JP
    rom[0x101] = 0x50  # Low byte
    rom[0x102] = 0x01  # High byte
    rom[0x103] = 0x00  # NOP padding

    # Nintendo logo at 0x0104
    for i, b in enumerate(NINTENDO_LOGO):
        rom[0x104 + i] = b

    # Title at 0x0134 (max 16 chars for older, 11 for newer)
    title = b'DEMO'
    for i, b in enumerate(title[:16]):
        rom[0x134 + i] = b

    # Cart type at 0x0147: ROM only
    rom[0x147] = 0x00

    # ROM size at 0x0148: 32KB
    rom[0x148] = 0x00

    # RAM size at 0x0149: None
    rom[0x149] = 0x00

    # Destination at 0x014A: Japanese
    rom[0x14A] = 0x00

    # Old licensee at 0x014B
    rom[0x14B] = 0x00

    # Version at 0x014C
    rom[0x14C] = 0x00

    # Header checksum at 0x014D
    checksum = 0
    for i in range(0x134, 0x14D):
        checksum = (checksum - rom[i] - 1) & 0xFF
    rom[0x14D] = checksum

    # Global checksum at 0x014E-0x014F (not validated by GB)
    rom[0x14E] = 0x00
    rom[0x14F] = 0x00

    # Code at 0x0150
    code = assemble_code()
    for i, b in enumerate(code):
        rom[0x150 + i] = b

    # Font data at 0x0200
    font = generate_font_tiles()
    for i, b in enumerate(font):
        rom[0x200 + i] = b

    return bytes(rom)

def main():
    rom = generate_demo_rom()

    # Write ROM file
    with open('demo.gb', 'wb') as f:
        f.write(rom)

    print(f"Generated demo.gb ({len(rom)} bytes)")

    # Also generate C array for embedding
    with open('demo_rom.h', 'w') as f:
        f.write("// Auto-generated demo ROM\n")
        f.write("// Generated by generate_demo_rom.py\n\n")
        f.write("#ifndef DEMO_ROM_H\n")
        f.write("#define DEMO_ROM_H\n\n")
        f.write(f"static const unsigned char demo_rom[{len(rom)}] = {{\n")

        for i in range(0, len(rom), 16):
            f.write("    ")
            for j in range(16):
                if i + j < len(rom):
                    f.write(f"0x{rom[i+j]:02X}, ")
            f.write("\n")

        f.write("};\n\n")
        f.write("#endif // DEMO_ROM_H\n")

    print("Generated demo_rom.h (C header for embedding)")

if __name__ == '__main__':
    main()
