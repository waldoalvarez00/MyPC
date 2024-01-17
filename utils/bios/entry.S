// Copyright Jamie Iles, 2017
// Copyright Waldo Alvarez, 2023
// https://pipflow.com

// This file is part of s80x86.
//
// s80x86 is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// s80x86 is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with s80x86.  If not, see <http://www.gnu.org/licenses/>.

#include "macros.h"


.code16

.section .reset.text, "ax"
.globl _reset
_reset:
    ljmp $0xf000, $_start

.section .model, "a"
    .byte 0xff
    .byte 0x00

.section .entry.text, "ax"
.globl _start
_start:

    mov $1, %ax
    mov $0xfffe, %dx   // Move the port address 0xfffe into the dx register
    out %ax, %dx       // write the number of blinks for the led
    
    // Wait for SDRAM to initialize
    mov $0xfffc, %dx
    mov $1, %ax
1:
    in (%dx), %ax
    cmp $0x1, %ax
    jne 1b



    // Load segments from CS
    
    mov %cs, %ax
    mov %ax, %ss
    mov %ax, %ds
    mov %ax, %es

    // lets test memory with the BIOS stack space
    lea bios_start, %si
    dec %si // one lower
    
    xor %cx,%cx
    
test_ram1:

    # Write test pattern (0xAA) to memory location pointed by SI
    movb $0xAA, %al
    mov %al, (%si)

    # Read back from the same location and compare
    cmpb $0xAA, (%si)
    jne error1

    # Move to the next address
    dec %si
    inc %cx
    
    # Check if end of RAM is reached
    cmp $5, %cx
    jb test_ram1

    # If completed without errors, continue
    jmp ram_tested1
    
    error1:
    # Infinite loop with NOPs on error
.error_loop1:
    nop
    jmp .error_loop1
    
ram_tested1:

    // lets test memory with the BIOS stack space
    lea bios_start, %si
    dec %si // 2  lower
    dec %si
    
    xor %cx,%cx

test_ram2:
    // Write test pattern (0xAAAA) to memory location pointed by SI
    movw $0xAA55, %ax
    mov %ax, (%si)

    // Read back from the same location and compare
    cmpw $0xAA55, (%si)
    jne error2

    // Move to the next word address (2 bytes forward)
    add $2, %si
    inc %cx

    // Check if end of RAM is reached
    cmp $5, %cx
    jb test_ram2

    // If completed without errors, continue
    jmp ram_tested2

    error2:
    // Infinite loop with NOPs on error
   .error_loop2:
   nop
   jmp .error_loop2

ram_tested2:

    
    // Point to VGA/MCGA memory (0xB8000 in standard text mode)
    mov $0xB800, %ax
    mov %ax, %es
    xor %di, %di   // DI = 0, start of VGA/MCGA memory

    // Write 'H' to VGA/MCGA memory
    mov $0x0748, %ax  // 'H' character with attribute (light grey on black)
    stosw             // Store character and attribute

    // Write 'E' to VGA/MCGA memory
    mov $0x0745, %ax  // 'E' character with attribute
    stosw             // Store character and attribute

    // Write 'L' to VGA/MCGA memory
    mov $0x074C, %ax  // 'L' character with attribute
    stosw             // Store character and attribute

    // Write another 'L' to VGA/MCGA memory
    stosw             // 'L' is already in AX, just store it again

    // Write 'O' to VGA/MCGA memory
    mov $0x074F, %ax  // 'O' character with attribute
    stosw             // Store character and attribute




    
    mov %cs, %ax
    mov %ax, %es
    
    lea bios_start, %cx
    dec %cx
    mov %cx, %di
    xor %ax, %ax
    std
    rep stosb
    cld

    // Clear bss
    mov $bss_start, %di
    mov $bss_end, %cx
    sub $bss_start, %cx
    mov $0, %al
    rep stosb

    // Initialize rw data
    mov $data_start, %di
    mov $data_end, %cx
    sub $data_start, %cx
    mov $_data_load, %si
    rep movsb

    movw $stack_start, %sp

    jmp root

.section .data
bios_ss:
    .word 0xf000
bios_sw_sp:
    .word stack_start
bios_hw_sp:
    .word stack_start - 8192

.section .bss
saved_sw_ss: .word 0
saved_sw_sp: .word 0

.macro entry_fn name saved_ss_var saved_sp_var ss_var sp_var
.section .text, "ax"
.globl \name
\name:
    // Save current stack pointer, load BIOS stack
    mov %ss, %cs:\saved_ss_var
    mov %sp, %cs:\saved_sp_var
    mov %cs:\ss_var, %ss
    mov %cs:\sp_var, %sp

    // Save registers, setup stack frame
    sub $2, %sp
    push %es
    push %ds
    pusha
    mov %sp, %bp
    push %bp

    // Load flags from iret frame, store in callregs
    mov %cs:\saved_ss_var, %ds
    mov %cs:\saved_sp_var, %bx
    mov 0(%bx), %ax
    mov 6(%bx), %bx
    mov %bx, 20(%bp)

    // Use SS as DS inside the BIOS for stack-local variables that are passed
    // by address
    mov %ss, %bp
    mov %bp, %ds

    call *%ax
    // Discard regs pointer parameter
    add $2, %sp
    mov %sp, %bp

    // Write possibly updated flags to the iret frame
    mov 20(%bp), %ax
    mov %cs:\saved_ss_var, %ds
    mov %cs:\saved_sp_var, %bx
    mov %ax, 6(%bx)

    // Restore all regs apart from flags - the iret frame has been updated
    // already
    popa
    pop %ds
    pop %es
    add $2, %sp

    // Restore the callers stack
    mov %cs:\saved_ss_var, %ss
    mov %cs:\saved_sp_var, %sp
    add $2, %sp

    iret
.endm

entry_fn irq_entry, saved_sw_ss, saved_sw_sp, bios_ss, bios_sw_sp

stub_irq:
    iret

int_handler 0x1c, stub_irq

timer_irq:
    cli
    push %ds
    push %bx

    movw $0x40, %bx
    mov %bx, %ds
    xor %bx, %bx
    addb $1, 0x6c
    adcb $0, 0x6e

    // Handle 24 hour overflow flag
    cmpw $0x000f, 0x6c
    jne .Lno_overflow
    cmpw $0x0018, 0x6e
    jne .Lno_overflow

    movw $0, 0x6c
    movw $0, 0x6e
    incb 0x70

.Lno_overflow:
    pop %bx
    pop %ds

    int $0x1c

    push %ax
    movb $0x20, %al
    outb %al, $0x20
    pop %ax

    iret

int_handler 0x08, timer_irq

kbd_irq:
    push %ax
    movb $0x20, %al
    outb %al, $0x20
    pop %ax

    iret

int_handler 0x09, kbd_irq

.globl unused_int
unused_int:
    cld
    cli
    push $do_unused_int
    jmp irq_entry

.pushsection ".bios_date", "a"
    .ascii BIOS_BUILD_DATE
.popsection
