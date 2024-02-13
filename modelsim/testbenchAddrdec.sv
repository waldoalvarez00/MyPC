`timescale 1ns / 1ps

module io_decoder_tb;

// Testbench Signals
reg d_io;
reg data_m_access;
reg [19:1] data_m_addr;
wire leds_access;
wire sdram_config_access;
wire default_io_access;
wire uart_access;
wire spi_access;
wire irq_control_access;
wire pic_access;
wire timer_access;
wire bios_control_access;
wire vga_reg_access;
wire ps2_kbd_access;
wire ps2_mouse_access;
wire ppi_control_access;

// Instantiate the Unit Under Test (UUT)
AddressDecoderIO uut (
    .d_io(d_io),
    .data_m_access(data_m_access),
    .data_m_addr(data_m_addr),
    .leds_access(leds_access),
    .sdram_config_access(sdram_config_access),
    .default_io_access(default_io_access),
    .uart_access(uart_access),
    .spi_access(spi_access),
    .irq_control_access(irq_control_access),
    .pic_access(pic_access),
    .timer_access(timer_access),
    .bios_control_access(bios_control_access),
    .vga_reg_access(vga_reg_access),
    .ps2_kbd_access(ps2_kbd_access),
    .ps2_mouse_access(ps2_mouse_access),
    .ppi_control_access(ppi_control_access)
);

initial begin
    // Initialize Inputs
    d_io = 0;
    data_m_access = 0;
    data_m_addr = 0;

    // Wait 100 ns for global reset to finish
    #5;
    
    // Stimulus: Accessing address 3D8h
    d_io = 1;
    data_m_access = 1;
    //data_m_addr = 16'h03D8; // Address 3D8h

    data_m_addr = 16'hFFFE; // Address 3D8h

    // Wait for the design to process the input
    #10;
    
    // Check the result
    if (vga_reg_access === 1'b1) begin
        $display("Test passed: VGA register access is correctly set for address 3D8h.");
    end else begin
        $display("Test failed: VGA register access is not correctly set for address 3D8h.");
    end

    // Complete the simulation
    #10;
   
end

endmodule
