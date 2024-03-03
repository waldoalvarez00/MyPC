
//`default_nettype none

module AddressDecoderIO(


                    // Bus
                    input wire d_io,
                    input wire [19:1] data_m_addr,
                    input wire data_m_access,


                    // Select outputs
                    output reg   leds_access,
                    output reg   sdram_config_access,
                    output reg   default_io_access,
						  output reg   uart_access,
                    output reg   uart2_access,

                    output reg   irq_control_access,
                    output reg   pic_access,
                    output reg   timer_access,
                    output reg   bios_control_access,
                    output reg   vga_reg_access,
                    
                    output reg   ps2_mouse_access,
						  output reg   cga_reg_access,
						  output reg   mcga_reg_access,
                    output reg   ppi_control_access,
						  
						  output logic dma_chip_select,
                    output logic dma_page_chip_select
						  
						  
                    );
						  




/*

CRT Controller Registers: Ports 0x3D4 (Index Register) and 0x3D5 (Data Register) for the standard VGA CRT Controller.
 MCGA would use a subset of these registers.
 
Attribute Controller Registers: Ports 0x3C0 (Index/Data Register) and 0x3C1 (Data Read Register).

Graphics Controller Registers: Ports 0x3CE (Index Register) and 0x3CF (Data Register).

Sequencer Registers: Ports 0x3C4 (Index Register) and 0x3C5 (Data Register).

Palette Registers: Ports 0x3C8 (Palette Address Register), 0x3C9 (Palette Data Register), 
and sometimes 0x3C7 (Palette Status/Register Read).

Miscellaneous Output Register: Port 0x3CC (Read) and 0x3C2 (Write).

Input Status Registers: Ports 0x3C2 (Input Status #0) and 0x3DA (Input Status #1).

*/

always_comb begin

 $display("Address: %h, d_io: %b, data_m_access: %b", data_m_addr, d_io, data_m_access);

    // Initialize all accesses to 0
    leds_access          = 1'b0;
    sdram_config_access  = 1'b0;
    default_io_access    = 1'b0;
    uart_access          = 1'b0;
    
    irq_control_access   = 1'b0;
    pic_access           = 1'b0;
    timer_access         = 1'b0;
    bios_control_access  = 1'b0;
    mcga_reg_access      = 1'b0;
    ps2_mouse_access     = 1'b0;
    ppi_control_access   = 1'b0;
    cga_reg_access       = 1'b0;
    uart2_access         = 1'b0;
    dma_chip_select      = 1'b0;
    dma_page_chip_select = 1'b0;
	 
	 
	 // 000-00F  8237 DMA controller`
	 // 010-01F  8237 DMA Controller (PS/2 model 60 & 80), reserved (AT)
	 // 030-03F  8259A Slave Programmable Interrupt Controller (AT,PS/2)
	 // 040-05F  8253 or 8254 Programmable Interval Timer (PIT, see ~8253~)
	 
	 // 060-067  8255 Programmable Peripheral Interface  (PC,XT, PCjr)
	 // 060 8255 Port A keyboard input/output buffer (output PCjr)
	 // 061 8255 Port B output
	 // 062 8255 Port C input
	 // 063 8255 Command/Mode control register
	 
	 // 070 CMOS RAM/RTC, also NMI enable/disable (AT,PS/2, see RTC)
	 // 071 CMOS RAM data  (AT,PS/2)
	 
	 // 0A0 NMI Mask Register (PC,XT) (write 80h to enable NMI, 00h disable)
	 
	 // 0C0 TI SN76496 Programmable Tone/Noise Generator (PCjr)
	 
	 // 0F0-0FF  Math coprocessor (AT, PS/2)
	 
	 // 2A2-2A3  MSM58321RS clock

    // Determine access type based on conditions
	 
	 // wire    floppy0_chip_select   = ((({address[15:2], 2'd0} == 16'h03F0) || ({address[15:1], 1'd0} == 16'h03F4) || ({address[15:0]} == 16'h03F7)));
    if (d_io && data_m_access) begin
	 
	     if (data_m_addr[16:2] == 15'b0000_0000_0010_000) begin // 20h -> 21h (PIC)
            pic_access = 1'b1;
        end 
	     else if ({data_m_addr[16:5], 4'd0} == 16'h0000) begin  // 0x00 .. 0x1F
            dma_chip_select = 1'b1;
        end
		  else if ({data_m_addr[16:5], 4'd0} == 16'h0080) begin  // 0x80 .. 0x8F
            dma_page_chip_select = 1'b1;
        end
        else 
		  if ({data_m_addr[16:4], 3'd0} == 16'h03F8) begin
		      // UART Chip Select
            uart_access = 1'b1;
        end
        else if ({data_m_addr[16:4], 3'd0} == 16'h02F8) begin
		      // UART2 Chip Select
            uart2_access = 1'b1;
        end
        //if (data_m_addr[16:7] == 10'b0000_0011_11)  begin          // 3CXh = 3C0 -> 3DF
		  else if (data_m_addr[16:7] == 10'b0000_0010_11)  begin       // 2CXh = 2C0 -> 2DF Moved to non Standar
            mcga_reg_access = 1'b1;
        end else
		  if (data_m_addr[16:7] == 10'b0000_0011_11)  begin            // 3CXh = 3C0 CGA Access
            cga_reg_access = 1'b1;
        end
        else if (data_m_addr[16:1] == 16'b1111_1111_1111_1110) begin // FFFE
            leds_access = 1'b1;
        end
        else if (data_m_addr[16:1] == 16'b1111_1111_1111_1100) begin // FFFC
            sdram_config_access = 1'b1;
        end
        else if (data_m_addr[16:2] == 15'b1111_1111_1111_101) begin
            uart_access = 1'b1;
        end
        else if (data_m_addr[16:2] == 15'b1111_1111_1111_011) begin
            irq_control_access = 1'b1;
        end
        else if (data_m_addr[16:2] == 15'b1111_1111_1110_110) begin
            bios_control_access = 1'b1;
        end
        else if (data_m_addr[16:3] == 14'b0000_0000_0100_00) begin  // 4Xh = x40 -> x43 (PIT)
            timer_access = 1'b1;
        end
        
        else if (data_m_addr[16:1] == 15'b1111_1111_1110_000) begin // FFD0h
            ps2_mouse_access = 1'b1;
        end
		  
		  else if (data_m_addr[16:3] == 14'b0000_0000_0110_00) begin
		      ppi_control_access = 1'b1;
		  end
        
		  /*else if (data_m_addr[16:3] == 14'b0000_0000_0110_00) begin  // 62h 63h
		      if (data_m_addr[16:1] == 15'b0000_0000_0110_000)        // 60h 61h
              ps2_kbd_access = 1'b1;
				else
              ppi_control_access = 1'b1;
        end*/
		  
		  
		  
	 
        else begin
            default_io_access = 1'b1;
        end
    end
end

						  
/*
	

// Note, check for glitches	
always_comb begin
    leds_access = 1'b0;
    sdram_config_access = 1'b0;
    default_io_access = 1'b0;
    uart_access = 1'b0;
    spi_access = 1'b0;
    irq_control_access = 1'b0;
    pic_access = 1'b0;
    timer_access = 1'b0;
    bios_control_access = 1'b0;

    vga_reg_access = 1'b0;


    ps2_kbd_access = 1'b0;
    ps2_mouse_access = 1'b0;


    if (d_io && data_m_access) begin
        casez ({data_m_addr[15:1], 1'b0})
        16'b1111_1111_1111_1110: leds_access = 1'b1;
        16'b1111_1111_1111_1100: sdram_config_access = 1'b1;
        16'b1111_1111_1111_1010: uart_access = 1'b1;
        16'b1111_1111_1111_00z0: spi_access = 1'b1;
        16'b1111_1111_1111_0110: irq_control_access = 1'b1;
        16'b1111_1111_1110_1100: bios_control_access = 1'b1;
        16'b0000_0000_0100_00z0: timer_access = 1'b1;
        16'b0000_0000_0010_0000: pic_access = 1'b1;
// VGA
        16'b0000_0011_110z_zzzz: vga_reg_access = 1'b1;

// PS2
        16'b1111_1111_1110_0000: ps2_mouse_access = 1'b1;
        16'b0000_0000_0110_0000: ps2_kbd_access = 1'b1;

        default:  default_io_access = 1'b1;
        endcase
    end
end

*/
						  
endmodule