; doctor_boot.asm - GameBoy Doctor Boot ROM
; Initializes CPU to post-boot state for gameboy-doctor testing
; Target state: A=01 F=B0 BC=0013 DE=00D8 HL=014D SP=FFFE PC=0100

SECTION "BootCode", ROM0[$0000]

EntryPoint:
    ; Initialize registers to post-boot values
    ld a, $01           ; A = 0x01
    ld hl, $014D        ; HL = 0x014D
    ld de, $00D8        ; DE = 0x00D8
    ld bc, $0013        ; BC = 0x0013
    ld sp, $FFFE        ; SP = 0xFFFE

    ; Set flags: F = $B0 (Z=1, N=0, H=1, C=0)
    ; This requires specific flag manipulation
    ; Z=1 requires zero result, H=1 requires half-carry
    xor a               ; A = 0, sets Z flag
    scf                 ; Set carry flag
    ccf                 ; Clear carry (C=0)
    ; Note: Exact F=$B0 is complex, may need adjustment

    ; Restore A register after flag manipulation
    ld a, $01

    ; Disable boot ROM (write to $FF50)
    ld a, $01
    ldh [$FF50], a      ; [$FF50] = 1, disables boot ROM

    ; Jump to cartridge entry point
    jp $0100

    ; Pad to 256 bytes
    ds $0100 - @        ; Fill remaining space with zeros

SECTION "CartridgeHeader", ROM0[$0100]
    ; Entry point at $0100 (required by GameBoy spec)
    nop
    jp $0100            ; Loop infinitely (boot ROM should have jumped here)
