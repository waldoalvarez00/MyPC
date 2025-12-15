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

    //mov $1, %ax
    //mov $0xfffe, %dx   // Move the port address 0xfffe into the dx register
    //out %ax, %dx       // write the number of blinks for the led
    
    
    cli
    
    
    // Wait for SDRAM to initialize
    
    mov $0xfffc, %dx
    
x1b:
    in (%dx), %ax
    cmp $0x1, %ax
    jne x1b



    //--------------------------------------------------
    // Test if we can execute instructions from RAM
    // We will use something similar to call boot sector
    //--------------------------------------------------
    
    

    xor %ax, %ax
    
    // Initialize segment registers
    mov %ax, %es

    
    mov $0xE000, %ax // Set stack pointer
    mov %ax, %ss
 

    // Set BX to 0 for the destination address
    xor %bx, %bx

    // Write 10 NOPs to 0:0
    mov $0x90, %al 
    mov $10, %cx   
    
    
write_nops:
    mov %al, %es:(%bx)
    inc %bx
    loop write_nops



    // Write RETF instruction
    mov $0xCB, %al
    mov %al, %es:(%bx)

    // Prepare stack for far call to 0:0
    // Push return address (segment:offset) for RETF
    
    mov %cs, %ax          // Current code segment
    push %ax
    
    mov $after_call, %ax  // Offset of return address
    push %ax

    // Far call to 0:0
    ljmp $0x0000, $0x0000
    

    
    

after_call:

    // Execution resumes here after RETF if all went OK
    
    
    // ---------------------------------------------
    //  Test memory for adjacent writes and bytesel
    // ---------------------------------------------

    
    xor %si, %si
    mov %si, %es
    mov %si, %ds

    // Initialize data_area with specific values, working backwards
    movb $0xFF, %al         
    mov $6, %cx             



    // Fill with 0xFF

initialize_memory:
    
    movb %al, (%si)            
    inc %si                    
    loop initialize_memory     



    // Move SI back to point to the byte before bios_start
    xor %si, %si
    
    
    // Number of times to make the test (checks if RAM is refreshing
    // and not losing data content)
    
    mov $0x0FFF, %bx
    
dupcheck:    
    
    movb (%si), %al       
    cmpb $0xFF, %al         // Check if it's still 0xFF
    jne error3              

    // Write some bytes
    movb $0x12,  1(%si)     // Write 0x12
    movb $0x34,  3(%si)     // Write 0x34

    // Verify adjacent bytes have the initial value (0xFF here)
    // Bytesel test
    
    movb (%si), %al       
    cmpb $0xFF, %al         // Check if it's still 0xFF
    jne error3 
    
    movb 5(%si), %al       
    cmpb $0xFF, %al         // Check if it's still 0xFF
    jne error3
    
    movb 4(%si), %al       
    cmpb $0xFF, %al         // Check if it's still 0xFF
    jne error3
    
    
    dec %bx
    jnz dupcheck
    
    
    
    jmp ram_tested3
    
error3:

// Freeze on error

    nop
    nop
    nop

error31:

    nop
    nop
    nop
    jmp error31
    






ram_tested3:
    
    
    
    // ------------------------------------
    //  Test memory simple
    // ------------------------------------

    
    

    // lets test memory with the BIOS stack space
    lea bios_start, %si
    dec %si // one lower
    
    xor %cx,%cx
    
test_ram1:

    // Write test pattern (0xAA) to memory location pointed by SI
    movb $0xAA, %al
    mov %al, (%si)

    // Read back from the same location and compare
    cmpb $0xAA, (%si)
    jne error1

    // Move to the next address
    dec %si
    inc %cx
    
    // Check if end of RAM was reached
    cmp $105, %cx
    jb test_ram1

    // If completed without errors, continue
    jmp ram_tested1
    
    error1:
    // Infinite loop with NOPs on error
.error_loop1:
    nop
    jmp .error_loop1
    
ram_tested1:














    // lets test memory with the BIOS stack space
    lea bios_start, %si
    dec %si // 2  lower
    dec %si
    
    xor %cx,%cx

    mov $1234, %ax
    
test_ram2:
    // Write test number to memory location pointed by SI
    
    inc %ax
    mov %ax, (%si)

    // Read back from the same location and compare
    cmpw %ax, (%si)
    jne error2

    // Move to the next word address (2 bytes forward)

    dec %si  // Tests aligned and unaligned
    
    inc %cx

    // Check if end of RAM is reached
    cmp $105, %cx
    jb test_ram2

    // If completed without errors, continue
    jmp ram_tested2

    error2:
    // Infinite loop with NOPs on error
   .error_loop2:
   nop
   jmp .error_loop2

ram_tested2:

    
    



// Function: scrub_mem
// clears all memory

scrub_mem:
    xorw   %bx, %bx     // Clear BX for the initial segment
    cld                 // Clear direction flag for forward movement

scrub_loop:
    cmpw   $0xF000, %bx // Compare BX with 0xF000
    jge    end_scrub    // If BX >= 0xF000, jump to end

    // Inline memset_seg functionality
    movw   %bx, %es     // Set ES to the current segment
    xorw   %di, %di     // Clear DI to zero (destination offset)
    xorw   %ax, %ax     // Clear AX to zero (AL will be zero, as it's the lower byte of AX)
    movw   $0x8000, %cx // Set CX to the length (0x8000 words = 64kb)
    rep    stosw        // Repeat store string word

    addw   $0x1000, %bx // Increment BX by 0x1000 (next segment)
    jmp    scrub_loop

end_scrub:



    mov $0xD000, %ax
    mov %ax, %ss
    
    
    lea bios_start, %si
    dec %si // 2  lower
    dec %si
    
    //mov $0xFFFF, %cx
    //mov %cx, %sp
    
    mov %si, %sp


    push $3
    call xx__set_video_mode    
    
    call xx__clearscreen

/*
    xor %cx, %cx
    
    mov $0xB800, %ax // Load the frame buffer segment
    mov %ax, %es
     
    xor %di, %di  // Load the initial offset in the frame buffer
    
    mov $0x0720, %ax

loop_start3:
    cmp $2000, %cx       // Compare CX with 2000
    je loop_end3          // If CX == 2000, we're done

     
    mov %ax, %es:(%di)   
    add $2, %di          

    inc %cx              
    jmp loop_start3

loop_end3:

*/
    
    
    //mov $0x20, %al   // Move the value 32 (1 << 5) into AL
    //mov $0x3d9, %dx  // Move the port number 0x3d9 into DX
    //out %al, %dx     // Output the value in AL to the port in DX
    
    
    
    
    // Point to VGA/MCGA memory (0xB8000 in standard text mode)
    mov $0xB800, %ax
    mov %ax, %es
    xor %di, %di   // DI = 0, start of VGA/MCGA memory

    // Write 'H' to VGA/MCGA memory (e.g., Red on Black)
    mov $0x0448, %ax  // 'H' character with red foreground
    stosw             

    // Write 'E' to VGA/MCGA memory (e.g., Green on Black)
    mov $0x0245, %ax  // 'E' character with green foreground
    stosw             

    // Write 'L' to VGA/MCGA memory (e.g., Blue on Black)
    mov $0x014C, %ax  // 'L' character with blue foreground
    stosw             

    // Write another 'L' to VGA/MCGA memory (e.g., Magenta on Black)
    mov $0x054C, %ax  // 'L' character with magenta foreground
    stosw             

    // Write 'O' to VGA/MCGA memory (e.g., Cyan on Black)
    mov $0x034F, %ax  // 'O' character with cyan foreground
    stosw             
    
    
    mov $0x034F, %ax
    stosw
    
    mov $0x034F, %ax
    stosw
    

    
    
    // Setup stack
   
   
   /*
    
    mov $0xE000, %ax
    mov %ax, %ss
    mov %ax, %es
    
    mov %cs, %ax
    mov %ax, %ds
    //mov %ax, %gs
    //mov %ax, %fs
    
    // clear the stack
    
    mov $0xFFFF, %cx
    dec %cx
    
    mov %cx, %di
    mov %cx, %sp
    
    xor %ax, %ax
    std
    rep stosb
    //cld
    
    mov %cs, %ax
    mov %ax, %es

    // Clear bss
    //mov $bss_start, %di
    //mov $bss_end, %cx
    //sub $bss_start, %cx
    //mov $0, %al
    //rep stosb

    // Initialize rw data
    //mov $data_start, %di
    //mov $data_end, %cx
    //sub $data_start, %cx
    //mov $_data_load, %si
    //rep movsb

    //movw $stack_start, %sp
    



*/
    
    
    
    // ------------------------------------
    //  Test stack
    // ------------------------------------
    
    testsp:

    // Initialize registers with a pattern
    mov $0xAAAA, %ax
    mov $0xBBBB, %bx
    mov $0xCCCC, %cx
    mov $0xDDDD, %dx
    mov $0xEEEE, %si
    mov $0xFFFF, %di
    // SP (Stack Pointer) should not be set as it changes during push/pop

    // Push registers onto the stack
    push %ax
    push %bx
    push %cx
    push %dx
    push %si
    push %di

    // Pop values into different registers
    pop %di
    pop %si
    pop %dx
    pop %cx
    pop %bx
    pop %ax

    // jump to error handler if mismatch
    cmp $0xAAAA, %ax
    je check_bx
    jmp error_handler

check_bx:
    cmp $0xBBBB, %bx
    je check_cx
    jmp error_handler

check_cx:
    cmp $0xCCCC, %cx
    je check_dx
    jmp error_handler

check_dx:
    cmp $0xDDDD, %dx
    je check_si
    jmp error_handler

check_si:
    cmp $0xEEEE, %si
    je check_di
    jmp error_handler

check_di:
    cmp $0xFFFF, %di
    je all_ok
    jmp error_handler

all_ok:
    
    
    
    
    /*
    error656:

    nop
    nop
    nop
    jmp error656
    */
    


    


    mov %cs, %ax
    mov %ax, %es
    mov %ax, %ds
    
    
    jmp root

error_handler:
    // Infinite loop of NOPs
    nop
    jmp error_handler
    


// Constants
.set PIC_COMMAND, 0x20
.set PIC_DATA, 0x21
.set PIC_ICW1_INIT, 0x10    # 1 << 4
.set PIC_ICW1_SINGLE, 0x02  # 1 << 1
.set PIC_ICW1_ICW4, 0x01    # 1 << 0
.set PIC_ICW4_8086, 0x01    # 1 << 0


xx__irq_init:
    mov    $PIC_COMMAND, %dx        # Load PIC_COMMAND port address into dx
    movb    $PIC_ICW1_INIT | PIC_ICW1_SINGLE | PIC_ICW1_ICW4, %al
    outb    %al, %dx                 # Send command to PIC_COMMAND

    mov    $PIC_DATA, %dx           # Load PIC_DATA port address into dx
    movb    $0x08, %al
    outb    %al, %dx                 # Send data to PIC_DATA

    movb    $PIC_ICW4_8086, %al
    outb    %al, %dx                 # Send ICW4 to PIC_DATA

    movb    $0xFF, %al               # ~0
    outb    %al, %dx                 # Mask all IRQs

    call    xx__irq_ack
    ret
    

xx__irq_enable:
    // irq_num is passed through the stack
    mov    PIC_DATA, %dx
    inb     %dx, %al
    mov     4(%bp), %cl   # load irq_num
    notb    %cl
    andb    %cl, %al
    outb    %al, %dx
    ret


xx__irq_disable:

    // irq_num is passed through the stack
    mov    PIC_DATA, %dx
    inb     %dx, %al
    mov     4(%bp), %cl   # load irq_num
    shlb    %cl, %al
    orb     %cl, %al
    outb    %al, %dx
    ret


xx__irq_ack:
    movb    $0x20, %al
    outb    %al, $0x20
    ret


   


xx__set_cursor_scan_start:
    push %bp
    mov %sp, %bp

    mov 6(%bp), %ax      // Move 'scan_start' into AX (16-bit promoted)
    and $0x20, %al       // Check if 5th bit of scan_start is set
    jz no_disable_cursor 

    mov 6(%bp), %ax      // Reload 'scan_start' into AX
    and $0x0F, %al       // Isolate lower 4 bits
    or $0x10, %al        // Set the 5th bit (0x10)
    jmp write_crtc       

no_disable_cursor:
    mov 6(%bp), %ax      

write_crtc:
    push %ax             
    push $0x0a           
    call xx__crtc_reg_write  
    add $4, %sp          

    pop %bp
    ret
    
    
    
    
xx__set_cursor_scan_end:
    push %bp
    mov %sp, %bp

    mov 6(%bp), %ax      // Move 'scan_end' into AX (16-bit promoted)

    push %ax             
    push $0x0b           
    call xx__crtc_reg_write  
    add $4, %sp          

    pop %bp
    ret
    
    
    
    
xx__crtc_reg_write:
    push %bp        
    mov %sp, %bp    

    mov 6(%bp), %ax // Move 'reg' (first argument) into AX (16-bit)
    mov $0x3d4, %dx // Move the port number 0x3d4 into DX
    out %al, %dx    // Output the lower byte of AX (AL) to the port in DX

    mov 8(%bp), %ax // Move 'val' (second argument) into AX (16-bit)
    mov $0x3d5, %dx // Move the port number 0x3d5 into DX
    out %al, %dx    // Output the lower byte of AX (AL) to the port in DX

    pop %bp         
    ret             
    
    
    
    
xx__writew:
    push %bp
    mov %sp, %bp

    // Save DS register
    push %ds

    // Load segment into DS
    movw 4(%bp), %ax  // Load segment from stack
    mov %ax, %ds

    // Load address into BX
    movw 6(%bp), %bx  // Load address from stack

    // Load val into AX
    movw 8(%bp), %ax  // Load val from stack

    // Write AX to the memory location pointed by DS:BX
    mov %ax, %ds:(%bx)

    pop %ds
    pop %bp
    ret
    
    
    
    
    
    
xx__clearscreen:



    xor %cx, %cx
    
    
    mov $0xB800, %ax // Load the frame buffer segment
    mov %ax, %es
    
    
    mov $0x0720, %ax
    
    xor %di, %di  // Load the initial offset in the frame buffer

loop_start:
    cmp $2000, %cx       // Compare CX with 2000
    je loop_end          // If CX == 2000, we're done

         
    mov %ax, %es:(%di)   
    add $2, %di          

    inc %cx              
    jmp loop_start       

loop_end:

    ret
    
    
    
    
    
    
    
xx__set_video_mode:
    push %bp
    mov %sp, %bp

    // Get mode from function argument
    mov 4(%bp), %ax

    // Compare mode and jump to corresponding case
    cmp $0x2, %ax
    je mode_2_or_3
    cmp $0x3, %ax
    je mode_2_or_3
    cmp $0x4, %ax
    je mode_4_or_5
    cmp $0x5, %ax
    je mode_4_or_5
    cmp $0x13, %ax
    je mode_13
    jmp default_case

mode_2_or_3:

    
    
    movw $0x3c0, %dx
    mov $0x0c, %al
    out %al, %dx
    
    movw $0x3d8, %dx
    mov $0x09, %al
    out %al, %dx
    
    movw $0x0, xx_in_video_mode // We are in text mode
    
    //push $0x07
    //push $25
    //push $79
    //push $0
    //push $24
    //push $0
    //call xx__scroll_up
    //add $12, %sp
    jmp end_function

mode_4_or_5:

   
    
    
    movw $0x3c0, %dx
    mov $0x0c, %al
    out %al, %dx
    
    movw $0x3d8, %dx
    mov $0x0a, %al
    out %al, %dx
    
    
    
    push $20000
    push $0
    push $0x8000 //frame_buffer_offset
    push $0xb000 //frame_buffer_segment
    call xx__memset_seg
    add $8, %sp
    movw $0x1, xx_in_video_mode
    jmp end_function

mode_13:
    
    call xx__restore_dac
    
    movw $0x3c0, %dx
    mov $0x41, %al
    out %al, %dx
    
    movw $0x3d8, %dx
    mov $0x0a, %al
    out %al, %dx
    
    
    push $64000
    push $0
    push $0
    push $0xa000 //vga_frame_buffer_segment
    call xx__memset_seg
    add $8, %sp
    movw $0x1, xx_in_video_mode
    jmp end_function

default_case:
    mov $-1, %ax
    jmp end_function

end_function:
    mov %bp, %sp
    pop %bp
    ret
    
    
    
    
    
    
    
    
    
    
xx__clear_row:
    push %bp
    mov %sp, %bp

    push %ax
    push %bx
    push %cx
    push %dx

    mov 4(%bp), %al  // Load row into AL (8-bit)
    mov 6(%bp), %bl  // Load col_left into BL (8-bit)
    mov 8(%bp), %cl  // Load col_right into CL (8-bit)
    mov 10(%bp), %dl // Load attr into DL (8-bit)

    mov %dl, %ah    // Move attr to AH (8-bit)
    mov $0x20, %al  // Load space character into AL (8-bit)
    shl $8, %ax     // AX is now 16-bit for the blank character
    or $0x20, %al   // Combine with space character (still 16-bit)

col_loop:
        cmp %bl, %cl
        jg end_col_loop

        // Zero-extend BL (column) to AX for address calculation
        xor %ax, %ax   
        mov %bl, %al   // Move BL (column) to AL, zero-extending to AX

        // Use BX for row calculation to stay in 16-bit
        
        mov %al, %bh      // Load row into BH
        xor %bl, %bl      // Clear BL to make full BX = row
        mov $80, %ax      // AX = 80 (number of columns)
        mul %bh           // AX = AX * row
        add %ax, %bx      // BX = row * 80 + col
        shl $1, %bx       // BX *= 2 (each character is 2 bytes)
        add $0x8000, %bx  // Add frame buffer offset
        
        /*
        
        // Row calculation without MUL, using shifts and adds
        mov %al, %bh        # Load row into BH
        xor %bl, %bl        # Clear BL to make full BX = row
        mov $0x40, %dx      # DX = 64 (2^6)
        shl $4, %dx         # DX *= 16 (2^4), DX = 1024
        add %dx, %dx        # DX *= 2, DX = 2048
        sub $0x40, %dx      # DX -= 64, DX = 1984 (80 * row)
        mul %bh             # AX = DX * row (result in AX)
        add %ax, %bx        # BX = row * 80 + col
        shl $1, %bx         # BX *= 2 (each character is 2 bytes)
        add $0x8000, %bx    # Add frame buffer offset
        
        */

        // Call writew
        push %dx         // Push val (blank character)
        push %bx         // Push address
        push $0xa000     // Push framebuffer segment
        call xx__writew
        add $6, %sp      // Clean up the stack

        inc %bl          // Increment column
        jmp col_loop

end_col_loop:
    pop %dx
    pop %cx
    pop %bx
    pop %ax
    pop %bp
    ret








xx__readw:
    push %bp             // Save base pointer
    mov %sp, %bp         // Set base pointer to stack pointer

    push %ds             
    mov 6(%bp), %ax      // Load segment argument into AX
    mov %ax, %ds         // Set DS to segment
    mov 8(%bp), %bx      // Load address argument into BX
    movw (%bx), %ax      // Read word at DS:BX into AX
    pop %ds              

    mov %bp, %sp         // Restore stack pointer
    pop %bp              
    ret                  // Return with value in AX

    
    
    
    
    

xx__memset_seg:
    push %bp
    mov %sp, %bp

    // Save registers that will be modified
    push %ax
    push %es
    push %cx
    push %di

    // Load function arguments into registers
    // dseg -> es, dst -> di, v -> al, len -> cx
    
    mov 4(%bp), %ax  // Load dseg
    mov %ax, %es     // Set es to dseg
    mov 6(%bp), %di  // Load dst offset
    mov 8(%bp), %al  // Load v
    mov 10(%bp), %cx // Load len

    // Clear Direction Flag (cld) to increment DI in stosb
    cld

    // Repeat Store String Byte (stosb) from AL to ES:DI for CX times
    rep stosb // change me to StosW

    // Restore modified registers
    pop %di
    pop %cx
    pop %es
    pop %ax

    // Restore base pointer and return
    pop %bp
    ret



// Assuming the init_dac array is properly allocated in data segment


xx__save_init_dac:
    push %bp
    mov %sp, %bp

    // outb(0x3c7, 0x0)
    mov $0x0, %al
    mov $0x3c7, %dx
    out %al, %dx

    
    xor %cx, %cx  // cx will be our loop counter (i)

loop_save_start:
    cmp $256, %cx
    jge loop_save_end

    // c.r = inb(0x3c9)
    mov $0x3c9, %dx 
    in %dx, %al
    mov %al, %ah  // Temporarily store r in ah

    // c.g = inb(0x3c9)
    in %dx, %al
    mov %al, %dh  // Temporarily store g in dh

    // c.b = inb(0x3c9)
    in %dx, %al
    // al now contains b

    // Calculating offset in init_dac array
    // Offset = i * sizeof(struct dac_color)
    mov %cx, %bx   // bx = i
    shl $2, %bx    // Multiply by sizeof(struct dac_color) = 4 (3 bytes + 1 byte padding)
    add xx__init_dac, %bx // Add base of init_dac array

    // Storing r, g, b in init_dac[i]
    mov %ah, (%bx) // Store r
    mov %dh, 1(%bx) // Store g
    mov %al, 2(%bx) // Store b


    inc %cx
    jmp loop_save_start

loop_save_end:
    pop %bp
    ret

    
    
// The function first calculates the initial offsets for the source and destination rows in the frame buffer.
//It then enters a loop (col_loop), where it reads a word from the source address using xx__readw and writes it to the destination address using xx__writew.
//The loop continues until all specified columns are processed.
//The stack is cleaned up after each call to xx__readw and xx__writew.
//Register usage is kept consistent with the calling convention, and necessary registers are preserved.

xx__copy_row:
    push %bp
    mov %sp, %bp

    push %si
    push %di     

    mov 8(%bp), %al       // Load dst_row
    mov 9(%bp), %ah       // Load src_row
    mov 10(%bp), %cl      // Load col_left
    mov 11(%bp), %dl      // Load col_right

    # Calculate initial source offset
    xor %bx, %bx          
    mov %ah, %bl          // BL = src_row
    mov $80, %ax          // AX = 80 (number of columns)
    mul %bl               // DX:AX = src_row * 80
    add %cl, %al          // AL = (src_row * 80) + col_left
    shl $1, %ax           // AX *= 2 (word address)
    add $0x8000, %ax      // Add frame_buffer_offset
    mov %ax, %si          // SI = source offset

    # Calculate initial destination offset
    xor %bx, %bx          
    mov %al, %bl          // BL = dst_row
    mov $80, %ax          // AX = 80 (number of columns)
    mul %bl               // DX:AX = dst_row * 80
    add %cl, %al          // AL = (dst_row * 80) + col_left
    shl $1, %ax           // AX *= 2 (word address)
    add $0x8000, %ax
    mov %ax, %di          // DI = destination offset

copy_col_loop:
    cmp %dl, %cl
    jg end_col_loop2

    # Read from source
    push %di
    push %si
    push $0xa000          # Frame buffer segment
    call xx__readw
    add $6, %sp           
    mov %ax, %dx          # DX = data read


    push %dx
    push %di
    push $0xa000          # Frame buffer segment
    call xx__writew
    add $6, %sp           

    # Increment column and update offsets
    inc %cl
    add $2, %si           
    add $2, %di           
    jmp copy_col_loop

end_col_loop2:
    pop %di               
    pop %si               
    pop %bp
    ret


    
    

xx__scroll_up:
    push %bp             
    mov %sp, %bp         

    // Local variable - row
    sub $1, %sp          // Make space for 'row' on the stack

    // Initialize row with row_top
    mov 8(%bp), %al      // Move row_top into AL
    mov %al, -1(%bp)     // Store AL (row_top) in 'row'


begin_for_loop:
    // Load row into AL
    mov -1(%bp), %al

    # Check if row <= row_bottom
    cmp 9(%bp), %al     // Compare row_bottom with row
    jg end_for_loop     // If row > row_bottom, jump to end_for_loop

    # Check if row + scroll_count > row_bottom
    mov 14(%bp), %cl    // Move scroll_count into CL
    add %cl, %al        // Add scroll_count to row
    cmp 9(%bp), %al     // Compare row + scroll_count with row_bottom
    jg call_clear_row   // If row + scroll_count > row_bottom, call clear_row

    
    call_copy_row:
        push -1(%bp)           // Push row
        push 14(%bp)           // Push scroll_count
        push 10(%bp)           // Push col_left
        push 11(%bp)           // Push col_right
        push 12(%bp)           // Push blank_attr
        call xx__copy_row
        add $10, %sp           
        jmp increment_row

    
    call_clear_row:
        push -1(%bp)           // Push row
        push 10(%bp)           // Push col_left
        push 11(%bp)           // Push col_right
        push 12(%bp)           // Push blank_attr
        call xx__clear_row
        add $8, %sp           

    // Increment row and loop back
    increment_row:
        mov -1(%bp), %al       // Load row
        inc %al                
        mov %al, -1(%bp)       // Store back row
        jmp begin_for_loop     

end_for_loop:
    mov %bp, %sp             
    pop %bp                  
    ret                      
    
    
    
    
    
   
xx__restore_dac:

    push %bp
    mov %sp, %bp

    // Set DAC address port to 0
    mov $0x3c8, %dx        // DX = 0x3c8, port for setting DAC address
    xor %ax, %ax           
    out %al, %dx           

    // Initialize m (counter) to 0, stored in CX
    xor %cx, %cx           

    // Start of the for loop
for_loop:
    cmp $256, %cx          
    jge end_for            // If m >= 256, exit loop

    // Calculate address of init_dac[m]
    mov %cx, %bx           // BX = m
    shl $1, %bx            // BX = BX * 2
    add %bx, %bx           // BX = BX * 2, now BX = 4 * m
    lea xx__init_dac(%bx), %si // SI = address of init_dac[m]

    // Output R value
    mov %ds:(%si), %al     // Load R value of init_dac[m] into AL
    mov $0x3c9, %dx        // DX = 0x3c9, port for setting DAC data
    out %al, %dx           // Send R value to port 0x3c9

    // Output G value
    inc %si                // Point to G value
    mov %ds:(%si), %al     // Load G value of init_dac[m] into AL
    out %al, %dx           // Send G value to port 0x3c9

    // Output B value
    inc %si                // Point to B value
    mov %ds:(%si), %al     // Load B value of init_dac[m] into AL
    out %al, %dx           // Send B value to port 0x3c9

    // Increment m and loop back
    inc %cx                
    jmp for_loop           

end_for:
    mov %bp, %sp           
    pop %bp                
    ret                    

    

    
    
    /*
    
    
    display_init:
	enterw	$6-2,	$0
	movw	$967,	%dx
	xorb	%al,	%al

	outb %al, %dx

	movw	$init_dac,	%bx
	leaw	768(%bx),	%cx
	movw	$969,	%dx
	
	
xxL165:

	inb %dx, %al



	movb	%al,	-4(%bp)


	inb %dx, %al


	movb	%al,	(%bx)
	inb %dx, %al

	movb	%al,	1(%bx)
	movb	-4(%bp),	%al
	movb	%al,	2(%bx)
	addw	$3,	%bx
	cmpw	%cx,	%bx
	jne	xxL165
	
	
	pushw	$3
	call	xx__set_video_mode
	addw	$2,	%sp
	movw	$-32768,	%bx
	xorw	%dx,	%dx
	movw	$-20480,	%ax
xxL166:
	leaw	160(%bx),	%cx
xxL167:
	movw	%ax,	%ds
	movw	$1824,	(%bx)
	addw	$2,	%bx
	cmpw	%bx,	%cx
	jne	.L167
	cmpw	$-28768,	%cx
	jne	.L166
	movw	%dx,	-4(%bp)
	movw	$64,	%ax
	movw	%ax,	%ds
	movb	$3,	73
	movw	$80,	74
	movb	$24,	132
	movw	$980,	99
	movw	$2561,	137
	pushw	$7
	pushw	$7
	pushw	%ss
	popw	%ds
	call	xx__set_cursor_shape
	movw	-4(%bp),	%dx
	movb	%dl,	-1(%bp)
	movb	%dl,	-2(%bp)
	leaw	-2(%bp),	%ax
	pushw	%ax
	call	xx_write_cursor
	movw	$985,	%dx
	movb	$32,	%al

	outb %al, %dx

	leavew
	ret
    
    
    
    
    
xx__set_video_mode:
	pushw	%di
	enterw	$2-2,	$0
	cmpw	$19,	6(%bp)
	ja	xxL60
	movw	6(%bp),	%bx
	shlw	$1,	%bx
	jmp	*xxL56(%bx)
	.section	.rodata
	.p2align	1
	.p2align	2
xxL56:
	.hword	xxL60
	.hword	xxL60
	.hword	xxL55
	.hword	xxL55
	.hword	xxL57
	.hword	xxL57
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL60
	.hword	xxL58

xxL58:
	movw	$968,	%dx
	xorb	%al,	%al

	outb %al, %dx

	movw	$init_dac,	%bx
	leaw	768(%bx),	%cx
	movw	$969,	%dx
xxL59:
	movb	(%bx),	%al

	outb %al, %dx

	movb	1(%bx),	%al

	outb %al, %dx

	movb	2(%bx),	%al

	outb %al, %dx

	addw	$3,	%bx
	cmpw	%cx,	%bx
	jne	.L59
	movw	$960,	%dx
	movb	$65,	%al

	outb %al, %dx
	movw	$984,	%dx
	movb	$10,	%al

	outb %al, %dx

	xorw	%di,	%di
	movw	$-1536,	%cx
	xorb	%dl,	%dl
	movw	$-24576,	%ax

	push %ax
        push %es
        push %cx
        push %di
        cld
        mov %ax, %es
        mov %dl, %al
        mov %cx, %cx
        rep stosb
        pop %di
        pop %cx
        pop %es
        pop %ax


	movw	$1,	_in_video_mode
	movw	%di,	%ax
	leavew
	popw	%di
	ret
    
    
    */
    
    
    

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
xx_in_video_mode: .word 0

// Define an array of 256 elements, each 3 bytes long
xx__init_dac: .space 768








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
