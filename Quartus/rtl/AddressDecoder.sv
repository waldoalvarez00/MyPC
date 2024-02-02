
`default_nettype none

module AddressDecoderIO(


                    // Bus
                    input d_io,
                    input [19:1] data_m_addr,
                    input data_m_access,


                    // Select outputs
                    output leds_access,
						  output sdram_config_access,
                    output default_io_access,
                    output uart_access,
                    output spi_access,
                    output irq_control_access,
                    output pic_access,
                    output timer_access,
                    output bios_control_access,
                    output vga_reg_access,
                    output ps2_kbd_access,
                    output ps2_mouse_access
						  
                    );
						  

/*						  
always_comb begin
    // Initialize all accesses to 0
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

    // Determine access type based on conditions
    if (d_io && data_m_access) begin
        // Check for each access type
        if (data_m_addr[15:1] == 15'b1111_1111_1111_111) begin
            leds_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1111_110) begin
            sdram_config_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1111_101) begin
            uart_access = 1'b1;
        end
        else if (data_m_addr[15:3] == 13'b1111_1111_1111_00) begin
            spi_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1111_011) begin
            irq_control_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1110_110) begin
            bios_control_access = 1'b1;
        end
        else if (data_m_addr[15:3] == 13'b0000_0000_0100_00) begin // 4Xh = x40 -> x43 (PIT)
            timer_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b0000_0000_0010_000) begin // 20h
            pic_access = 1'b1;
        end
        else if (data_m_addr[15:5] == 11'b0000_0011_110) begin
            vga_reg_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1110_000) begin // FFD0h
            ps2_mouse_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b0000_0000_0110_000) begin // 60h
            ps2_kbd_access = 1'b1;
        end
        else begin
            default_io_access = 1'b1;
        end
    end
    // No need for else part; signals are already initialized to 0
end
*/


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
    // Initialize all accesses to 0
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

    // Determine access type based on conditions
    if (d_io && data_m_access) begin
        if (data_m_addr[15:1] == 15'b1111_1111_1111_111) begin
            leds_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1111_110) begin
            sdram_config_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1111_101) begin
            uart_access = 1'b1;
        end
        else if (data_m_addr[15:3] == 13'b1111_1111_1111_00) begin
            spi_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1111_011) begin
            irq_control_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1110_110) begin
            bios_control_access = 1'b1;
        end
        else if (data_m_addr[15:3] == 13'b0000_0000_0100_00) begin // 4Xh = x40 -> x43 (PIT)
            timer_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b0000_0000_0010_000) begin // 20h
            pic_access = 1'b1;
        end
        else if (data_m_addr[15:5] == 11'b0000_0011_110) begin // 3CXh = 3C0 -> 3CF
            vga_reg_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b1111_1111_1110_000) begin // FFD0h
            ps2_mouse_access = 1'b1;
        end
        else if (data_m_addr[15:1] == 15'b0000_0000_0110_000) begin // 60h
            ps2_kbd_access = 1'b1;
        end
        else begin
            // This is the explicit default case, only set if no other conditions are met.
            default_io_access = 1'b1;
        end
    end
    // No need for an else part; signals are already initialized to 0 at the beginning.
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