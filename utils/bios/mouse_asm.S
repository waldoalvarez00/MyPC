// Copyright Jamie Iles, 2017
//
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

#define PS2_CTRL_CLEAR (1 << 7)
#define MOUSE_DATA 0xffe0
#define MOUSE_STATUS 0xffe1
#define MOUSE_IRQ 7

.code16

.pushsection .bss
.globl mouse_driver_addr
mouse_driver_addr:
    .word 0
    .word 0

.globl mouse_packet
mouse_packet:
    .word 0
    .word 0
    .word 0

.globl mouse_driver_enabled
mouse_driver_enabled:
    .word 0
.globl mouse_nbytes
mouse_nbytes:
    .byte 0
.popsection

.globl update_mouse
update_mouse:
    pusha

    cmpw $0, %cs:mouse_driver_enabled
    jz 1f

    push %bx
    lea mouse_packet, %bx
    push %cs:0(%bx)
    push %cs:2(%bx)
    push %cs:4(%bx)
    push $0

    lcall *%cs:mouse_driver_addr
    add $8, %sp

    pop %bx
1:
    popa

    ret

mouse_irq:
    pusha

    movb $0x20, %al
    outb %al, $0x20

mouse_poll_loop:
    mov $MOUSE_STATUS, %dx
    in (%dx), %al
    test $0x10, %ax
    jz no_mouse_data

    mov %cs:mouse_nbytes, %si
    shl $1, %si
    lea mouse_packet, %bx

    mov $MOUSE_DATA, %dx
    in (%dx), %al
    mov %al, %cs:(%bx, %si)

    cmpb $0, %cs:mouse_nbytes
    jne .Lcheck_packet
    // Bit 4 should always be set in the first byte of a packet, attempt to
    // resynchronize if not.
    testb $0x08, %al
    jz incomplete_packet

.Lcheck_packet:
    incb %cs:mouse_nbytes
    cmpb $3, %cs:mouse_nbytes
    jne incomplete_packet

    movb $0, %cs:mouse_nbytes
    call update_mouse

incomplete_packet:
    jmp mouse_poll_loop

no_mouse_data:
    popa

    iret

int_handler (0x8 + MOUSE_IRQ), mouse_irq
