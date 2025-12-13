; simple_test.asm - Minimal test ROM for validating gameboy-doctor logger
; Contains 10 simple instructions with predictable behavior for hand-verification

SECTION "Header", ROM0[$0100]
    ; Standard GameBoy entry point
    nop                     ; 0100: NOP
    jp Start                ; 0101: JP $0150

    ; Pad to standard header location
    ds $0150 - @

SECTION "Main", ROM0[$0150]
Start:
    ; Instruction 1: NOP
    nop                     ; 0150: NOP

    ; Instruction 2: Load immediate value into A
    ld a, $42               ; 0151: LD A, $42

    ; Instruction 3: Copy A to B
    ld b, a                 ; 0153: LD B, A

    ; Instruction 4: Increment B
    inc b                   ; 0154: INC B

    ; Instruction 5: Load address into HL
    ld hl, $C000            ; 0155: LD HL, $C000

    ; Instruction 6: Store B to memory
    ld [hl], b              ; 0158: LD [HL], B

    ; Instruction 7: Increment HL
    inc hl                  ; 0159: INC HL

    ; Instruction 8: Load from memory into A
    ld a, [hl]              ; 015A: LD A, [HL]

    ; Instruction 9: Decrement A
    dec a                   ; 015B: DEC A

    ; Instruction 10: Infinite loop (test completion)
.loop:
    jr .loop                ; 015C: JR -2
