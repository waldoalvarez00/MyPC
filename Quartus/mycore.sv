//============================================================================
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//  This program is free software; you can redistribute it and/or modify it
//  under the terms of the GNU General Public License as published by the Free
//  Software Foundation; either version 3 of the License, or (at your option)
//  any later version.
//
//  This program is distributed in the hope that it will be useful, but WITHOUT
//  ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
//  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
//  more details.
//
//  You should have received a copy of the GNU General Public License along
//  with this program; if not, write to the Free Software Foundation, Inc.,
//  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
//
//============================================================================

module emu
(
	//Master input clock
	input         CLK_50M,

	//Async reset from top-level module.
	//Can be used as initial reset.
	input         RESET,

	//Must be passed to hps_io module
	inout  [48:0] HPS_BUS,

	//Base video clock. Usually equals to CLK_SYS.
	output        CLK_VIDEO,

	//Multiple resolutions are supported using different CE_PIXEL rates.
	//Must be based on CLK_VIDEO
	output        CE_PIXEL,

	//Video aspect ratio for HDMI. Most retro systems have ratio 4:3.
	//if VIDEO_ARX[12] or VIDEO_ARY[12] is set then [11:0] contains scaled size instead of aspect ratio.
	output [12:0] VIDEO_ARX,
	output [12:0] VIDEO_ARY,

	output  [7:0] VGA_R,
	output  [7:0] VGA_G,
	output  [7:0] VGA_B,
	
	output        VGA_HS,
	output        VGA_VS,
	output        VGA_DE,    // = ~(VBlank | HBlank)
	
	output        VGA_F1,
	output [1:0]  VGA_SL,
	output        VGA_SCALER, // Force VGA scaler
	output        VGA_DISABLE, // analog out is off

	input  [11:0] HDMI_WIDTH,
	input  [11:0] HDMI_HEIGHT,
	output        HDMI_FREEZE,

`ifdef MISTER_FB
	// Use framebuffer in DDRAM
	// FB_FORMAT:
	//    [2:0] : 011=8bpp(palette) 100=16bpp 101=24bpp 110=32bpp
	//    [3]   : 0=16bits 565 1=16bits 1555
	//    [4]   : 0=RGB  1=BGR (for 16/24/32 modes)
	//
	// FB_STRIDE either 0 (rounded to 256 bytes) or multiple of pixel size (in bytes)
	output        FB_EN,
	output  [4:0] FB_FORMAT,
	output [11:0] FB_WIDTH,
	output [11:0] FB_HEIGHT,
	output [31:0] FB_BASE,
	output [13:0] FB_STRIDE,
	input         FB_VBL,
	input         FB_LL,
	output        FB_FORCE_BLANK,

`ifdef MISTER_FB_PALETTE
	// Palette control for 8bit modes.
	// Ignored for other video modes.
	output        FB_PAL_CLK,
	output  [7:0] FB_PAL_ADDR,
	output [23:0] FB_PAL_DOUT,
	input  [23:0] FB_PAL_DIN,
	output        FB_PAL_WR,
`endif
`endif

	output        LED_USER,  // 1 - ON, 0 - OFF.

	// b[1]: 0 - LED status is system status OR'd with b[0]
	//       1 - LED status is controled solely by b[0]
	// hint: supply 2'b00 to let the system control the LED.
	output  [1:0] LED_POWER,
	output  [1:0] LED_DISK,

	// I/O board button press simulation (active high)
	// b[1]: user button
	// b[0]: osd button
	output  [1:0] BUTTONS,

	input         CLK_AUDIO, // 24.576 MHz
	output [15:0] AUDIO_L,
	output [15:0] AUDIO_R,
	output        AUDIO_S,   // 1 - signed audio samples, 0 - unsigned
	output  [1:0] AUDIO_MIX, // 0 - no mix, 1 - 25%, 2 - 50%, 3 - 100% (mono)

	//ADC
	inout   [3:0] ADC_BUS,

	//SD-SPI
	output        SD_SCK,
	output        SD_MOSI,
	input         SD_MISO,
	output        SD_CS,
	input         SD_CD,

	//High latency DDR3 RAM interface
	//Use for non-critical time purposes
	output        DDRAM_CLK,
	input         DDRAM_BUSY,
	output  [7:0] DDRAM_BURSTCNT,
	output [28:0] DDRAM_ADDR,
	input  [63:0] DDRAM_DOUT,
	input         DDRAM_DOUT_READY,
	output        DDRAM_RD,
	output [63:0] DDRAM_DIN,
	output  [7:0] DDRAM_BE,
	output        DDRAM_WE,

	//SDRAM interface with lower latency
	output        SDRAM_CLK,
	output        SDRAM_CKE,
	output [12:0] SDRAM_A,
	output  [1:0] SDRAM_BA,
	inout  [15:0] SDRAM_DQ,
	output        SDRAM_DQML,
	output        SDRAM_DQMH,
	output        SDRAM_nCS,
	output        SDRAM_nCAS,
	output        SDRAM_nRAS,
	output        SDRAM_nWE,

`ifdef MISTER_DUAL_SDRAM
	//Secondary SDRAM
	//Set all output SDRAM_* signals to Z ASAP if SDRAM2_EN is 0
	input         SDRAM2_EN,
	output        SDRAM2_CLK,
	output [12:0] SDRAM2_A,
	output  [1:0] SDRAM2_BA,
	inout  [15:0] SDRAM2_DQ,
	output        SDRAM2_nCS,
	output        SDRAM2_nCAS,
	output        SDRAM2_nRAS,
	output        SDRAM2_nWE,
`endif

	input         UART_CTS,
	output        UART_RTS,
	input         UART_RXD,
	output        UART_TXD,
	output        UART_DTR,
	input         UART_DSR,

	// Open-drain User port.
	// 0 - D+/RX
	// 1 - D-/TX
	// 2..6 - USR2..USR6
	// Set USER_OUT to 1 to read from USER_IN.
	input   [6:0] USER_IN,
	output  [6:0] USER_OUT,

	input         OSD_STATUS
);

///////// Default values for ports not used in this core /////////

assign ADC_BUS  = 'Z;
assign USER_OUT = '1;



assign {SD_SCK, SD_MOSI, SD_CS} = 'Z;

//assign {SDRAM_DQ, SDRAM_A, SDRAM_BA, SDRAM_CLK, SDRAM_CKE, SDRAM_DQML, SDRAM_DQMH, SDRAM_nWE, SDRAM_nCAS, SDRAM_nRAS, SDRAM_nCS} = 'Z;
//assign {SDRAM_CKE, SDRAM_DQML, SDRAM_DQMH} = 'Z;

assign {DDRAM_CLK, DDRAM_BURSTCNT, DDRAM_ADDR, DDRAM_DIN, DDRAM_BE, DDRAM_RD, DDRAM_WE} = '0;  

assign VGA_SL = 0;
assign VGA_F1 = 0;
assign VGA_SCALER  = 0;
assign VGA_DISABLE = 0;
assign HDMI_FREEZE = 0;

assign VGA_SL = 0;
assign VGA_F1 = 0;
assign VGA_SCALER = 0;

assign AUDIO_S = 0;
assign AUDIO_L = 0;
assign AUDIO_R = 0;
assign AUDIO_MIX = 0;

assign LED_DISK = 0;
assign LED_POWER = 0;
assign BUTTONS = 0;

//////////////////////////////////////////////////////////////////

wire [1:0] ar = status[122:121];

assign VIDEO_ARX = (!ar) ? 12'd4 : (ar - 1'd1);
assign VIDEO_ARY = (!ar) ? 12'd3 : 12'd0;

// Define constants for timing
 localparam integer BLINK_DURATION = 25_000_000; // 1 second at 25MHz
 localparam integer PAUSE_DURATION = 25_000_000; // 1 second pause

 //////////////////////////////////////////////////////////////////
    // Status Bit Map:
    //              Upper                          Lower
    // 0         1         2         3          4         5         6
    // 01234567890123456789012345678901 23456789012345678901234567890123
    // 0123456789ABCDEFGHIJKLMNOPQRSTUV 0123456789ABCDEFGHIJKLMNOPQRSTUV
    // XXXXX XXXXXXXXXXXXXXXXXXXXXXXXXX XXXXXXXX      xx
	 
`include "build_id.v" 
localparam CONF_STR = {
		"PCXT;UART115200:115200;",
		"S0,IMGIMAVFD,Floppy A:;",
		"S1,IMGIMAVFD,Floppy B:;",
		"OJK,Write Protect,None,A:,B:,A: & B:;",
		"-;",
		"S2,VHD,IDE 0-0;",
		"S3,VHD,IDE 0-1;",
		"OLM,2nd SD card,Disable,IDE 0-0,IDE 0-1;",
		"-;",
		"P1,System & BIOS;",
		"P1-;",
		"P1O3,Model,IBM PCXT,Tandy 1000;",
		"P1-;",
		"P1oC,PCXT CGA Graphics,Yes,No;",
		"P1oD,PCXT MCGA Graphics,Yes,No;",
		"P1O4,PCXT 1st Video,CGA,MCGA;",
		"P1-;",
		"P1O7,Boot Splash Screen,Yes,No;",
		"P1-;",
		"P1FC0,ROM,PCXT BIOS:;",
		"P1FC1,ROM,Tandy BIOS:;",
		"P1-;",
		"P1FC2,ROM,EC00 BIOS:;",
		"P1-;",
		"P1OUV,BIOS Writable,None,EC00,PCXT/Tandy,All;",
		"P1-;",	
		"P2,Audio & Video;",
		"P2-;",
		"P2OA,C/MS Audio,Enabled,Disabled;",
		"P2oAB,OPL2,Adlib 388h,SB FM 388h/228h, Disabled;",
		"P2o01,Speaker Volume,1,2,3,4;",
		"P2o23,Tandy Volume,1,2,3,4;",
		"P2o45,Audio Boost,No,2x,4x;",
		"P2o67,Stereo Mix,none,25%,50%,100%;",
		"P2-;",
		"P2O12,Scandoubler Fx,None,HQ2x,CRT 25%,CRT 50%;",
		"P2O89,Aspect ratio,Original,Full Screen,[ARC1],[ARC2];",
		"P2OT,Border,No,Yes;",
		"P2o8,Composite video,Off,On;",
		"P2OEG,Display,Full Color,Green,Amber,B&W,Red,Blue,Fuchsia,Purple;",
		"P2-;",
		"P3,Hardware;",
		"P3-;",
		"P3OB,Lo-tech 2MB EMS,Enabled,Disabled;",
		"P3OCD,EMS Frame,C000,D000,E000;",
		"P3-;",
		"P3o9,A000 UMB,Enabled,Disabled;",
		"P3-;",
		"P3ONO,Joystick 1, Analog, Digital, Disabled;",
		"P3OPQ,Joystick 2, Analog, Digital, Disabled;",
		"P3OR,Sync Joy to CPU Speed,No,Yes;",
		"P3OS,Swap Joysticks,No,Yes;",
		"P3oEF,RAM Type,Auto,SDRAM,DDR3;",
		"P3-;",	
		"-;",
		"R0,Reset & apply settings;",
		"J,Fire 1,Fire 2;",
		"V,v",`BUILD_DATE
	};

	
wire  [7:0] VGA_R_AUX1;
wire  [7:0] VGA_G_AUX1;
wire  [7:0] VGA_B_AUX1;

wire  [7:0] VGA_R_AUX2;
wire  [7:0] VGA_G_AUX2;
wire  [7:0] VGA_B_AUX2;
	
wire forced_scandoubler;
wire   [1:0] buttons;
wire [127:0] status;
wire  [10:0] ps2_key;



wire wps2_kbd_clk_2;
wire wps2_kbd_data_1;
wire wps2_kbd_clk_1;
wire wps2_kbd_data_2;


wire wps2_mouse_clk_out;
wire wps2_mouse_data_out;
wire wps2_mouse_clk_in;
wire wps2_mouse_data_in;


wire [15:0] sdram_sz;


hps_io #(.CONF_STR(CONF_STR), .PS2DIV(10), .PS2WE(1), .WIDE(1)) hps_io
(
	.clk_sys(sys_clk),
	.HPS_BUS(HPS_BUS),
	//.EXT_BUS(EXT_BUS),
	.gamma_bus(),

	.forced_scandoubler(forced_scandoubler),

	.buttons(buttons),
	.status(status),
	.status_menumask({status[5]}),
	
	.ps2_key(ps2_key),
	
	
	
	
	// ps2 keyboard emulation
	.ps2_kbd_clk_out(wps2_kbd_clk_2),
	.ps2_kbd_data_out(wps2_kbd_data_2),
	
	.ps2_kbd_clk_in(/*wps2_kbd_clk_1*/ 1'b1),
	.ps2_kbd_data_in(/*wps2_kbd_data_1*/ 1'b1),

	//input       [2:0] ps2_kbd_led_status,
	//input       [2:0] ps2_kbd_led_use,

	.sdram_sz(sdram_sz),
	.ps2_mouse_clk_out(wps2_mouse_clk_in),
	.ps2_mouse_data_out(wps2_mouse_data_in),
	.ps2_mouse_clk_in(wps2_mouse_clk_out),
	.ps2_mouse_data_in(wps2_mouse_data_out)
);

///////////////////////   CLOCKS   ///////////////////////////////

wire plock;

wire vga_clk;


pll pll
(
	.refclk(CLK_50M),
	.rst(0),
	.outclk_0(sys_clk), // 30 MHz
	.outclk_1(vga_clk), // 25.11 MHz
	.outclk_2(pit_clk),
	// outclk_3 - used for signaltap II 150 MHz
	.outclk_4(clk_mem), // 120 MHz
	.outclk_5(clk_uart),
	.locked(/*plock*/)
);






wire xreset = RESET; // | status[0] | buttons[1];

wire VSync;
wire HSync;



wire VSync_AUX1;
wire HSync_AUX1;
wire VGA_DE_AUX1;

wire VSync_AUX2;
wire HSync_AUX2;
wire VGA_DE_AUX2;













`ifdef CONFIG_SPEAKER
       //    output speaker_out,
`endif // CONFIG_SPEAKER
       //    input logic uart_rx,
       //    output logic uart_tx,
       //    output logic spi_sclk,
       //    output logic spi_mosi,
       //    input logic spi_miso,
       //    output logic spi_ncs);



/*`ifdef CONFIG_SPEAKER

wire speaker_gate_en;
wire speaker_timer_out;
wire speaker_data;
assign speaker_out = speaker_timer_out & speaker_data;
`define SPEAKER_TIMER_OUT speaker_timer_out
`define SPEAKER_DATA speaker_data
`define SPEAKER_GATE_EN_OUT speaker_gate_en
`define SPEAKER_GATE_EN_IN speaker_gate_en

`else // CONFIG_SPEAKER*/

`define SPEAKER_TIMER_OUT
`define SPEAKER_DATA_OUT
`define SPEAKER_DATA
`define SPEAKER_GATE_EN_OUT
`define SPEAKER_GATE_EN_IN 1'b0

/*`endif*/

//wire poweron_reset;
wire sys_clk;
//wire reset_n;
wire pll_locked;


wire cga_reg_access;
wire mcga_reg_access;
wire vga_reg_ack;
wire [15:0] vga_reg_data;
wire [15:0] cga_reg_data;

wire mcga_access;
wire cga_mem_access;
wire vga_ack;
wire [15:0] vga_data;
wire [15:0] cga_data;



wire [1:0] ir;
wire tdo;
wire tck;
wire tdi;
wire sdr;
wire cdr;
wire udr;
wire debug_stopped;
wire debug_seize;
wire debug_reset;
wire debug_run;
wire [7:0] debug_addr;
wire [15:0] debug_wr_val;
wire [15:0] debug_val;
wire debug_wr_en;



// DeMultiplexer

wire [15:0] io_data;

always @(*) begin
//always_comb begin
    if (leds_access) 
        io_data = leds_data;
    else if (uart_access) 
        io_data = uart_data;
    else if (uart2_access) 
        io_data = uart2_data;
    else if (irq_control_access) 
        io_data = irq_control_data;
    else if (pic_access) 
        io_data = pic_data;
    else if (timer_access) 
        io_data = timer_data;
    else if (bios_control_access) 
        io_data = bios_control_data;
    else if (mcga_reg_access) 
        io_data = vga_reg_data;
    else if (ps2_mouse_access) 
        io_data = ps2_mouse_data;
    else if (cga_reg_access) 
        io_data = cga_reg_data;
    else if (ppi_control_access)
        io_data = ppiout;
    else if (floppy_access)
        io_data = {8'b0, floppy_readdata};
    else
        io_data = 16'b0;
end
 
	 
wire [15:0] mem_data;

// Data bus
wire [19:1] data_m_addr;
wire [15:0] data_m_data_in = d_io ? io_data : mem_data;
wire [15:0] data_m_data_out;
wire data_m_access;
wire data_m_ack = data_mem_ack | io_ack;
wire data_m_wr_en;
wire [1:0] data_m_bytesel;

// Instruction bus
wire [19:1] instr_m_addr;
wire [15:0] instr_m_data_in;
wire instr_m_access;
wire instr_m_ack;

// Multiplexed I/D bus.
wire [19:1] q_m_addr;
wire [15:0] q_m_data_out;



wire [15:0] q_m_data_in = sdram_data |
            vga_data                 |
	         cga_data                 |
            bios_data;
	 
	 

	 
wire q_m_ack = cache_ack   |
               vga_ack     |
	            cga_mem_ack |
               bios_ack;
	 
	 
wire q_m_access;
wire q_m_wr_en;
wire [1:0] q_m_bytesel;

wire d_io;

wire sdram_access;
wire cache_ack;
wire [15:0] sdram_data;

wire leds_access;
wire leds_ack;
wire [15:0] leds_data;

wire bios_access;
wire bios_ack;
wire [15:0] bios_data;

wire bios_control_access;
wire bios_control_ack;

wire [15:0] bios_control_data;

wire sdram_config_access;
wire sdram_config_ack;
wire sdram_config_done;

//wire [15:0] sdram_config_data;


wire ps2_kbd_access;
wire ps2_kbd_ack;
wire [15:0] ps2_kbd_data;
wire ps2_kbd_intr;

wire ps2_mouse_access;
wire ps2_mouse_ack;
wire [15:0] ps2_mouse_data;
wire ps2_mouse_intr;


wire uart_access;
wire uart2_access;

wire uart1_ack;
wire uart2_ack;

wire [15:0] uart_data;
wire [15:0] uart2_data;

wire [7:0]  ppiout;



wire nmi;
wire [6:0] intr_test;
wire intr;
wire inta;
wire [7:0] irq;
wire irq_control_access;
wire irq_control_ack;
wire [15:0] irq_control_data;
wire pic_access;
wire pic_ack;
wire cga_reg_ack;
wire [15:0] pic_data;

wire [7:0] irqs = {1'b0, /* fdd */ fdd_interrupt, 1'b0, uart1_interrupt, uart2_interrupt, 1'b0, ps2_kbd_intr, timer_intr} | {1'b0, intr_test};

// Timer
wire pit_clk;
wire timer_intr;
wire timer_access;
wire timer_ack;
wire [15:0] timer_data;

wire default_io_access;
wire default_io_ack;

wire ppi_ack;



// Ack demultiplexing - Register output to prevent glitches

reg io_ack;

always @(posedge sys_clk) begin
    if (sdram_config_access)
        io_ack <= sdram_config_ack;
    else if (default_io_access)
        io_ack <= default_io_ack;
    else if (uart_access)
        io_ack <= uart1_ack;
    else if (uart2_access)
        io_ack <= uart2_ack;
    else if (leds_access)
        io_ack <= leds_ack;
    else if (irq_control_access)
        io_ack <= irq_control_ack;
    else if (pic_access)
        io_ack <= pic_ack;
    else if (cga_reg_access)
        io_ack <= cga_reg_ack;
    else if (timer_access)
        io_ack <= timer_ack;
    else if (mcga_reg_access)
        io_ack <= vga_reg_ack;
    else if (ps2_mouse_access)
        io_ack <= ps2_mouse_ack;
    else if (ppi_control_access)
        io_ack <= ppi_ack;
    else if (dma_chip_select | dma_page_chip_select)
        io_ack <= dma_ack;
    else if (bios_control_access)
        io_ack <= bios_control_ack;
    else if (floppy_access)
        io_ack <= floppy_ack;
    else
        io_ack <= 1'b0;
end

				  
				  
reg post_sdram_reset; // delayed reset after SDRAM is configured

always @(posedge sys_clk or posedge xreset) begin
    if (xreset) begin
        // When system is under reset, prepare to wait for SDRAM configuration
        post_sdram_reset <= 1'b1;
    end else if (sdram_config_done) begin
        // Once SDRAM configuration is done, clear the post SDRAM reset signal
        post_sdram_reset <= 1'b0 | status[0];
    end
end


always_comb begin
    if (DDRAM_BUSY) begin
        // No operation or minimal logic
    end
	 
	 if (DDRAM_DOUT_READY) begin
        // No operation or minimal logic
    end
	 
	 if (OSD_STATUS) begin
        // No operation or minimal logic
    end
	 
	 

end


// Avoids the CPU locking waiting for non existent IO
always_ff @(posedge sys_clk) begin

    default_io_ack <= default_io_access;
	 //data_m_data_out <= 0;
	 
end

	 
	 
logic   [7:0]   port_b_out;
logic   [7:0]   port_c_in;
reg     [7:0]   sw;

assign  sw = 8'b00101101; //hgc_mode ? 8'b00111101 : 8'b00101101; // PCXT DIP Switches (HGC or CGA 80)
assign  port_c_in[3:0] = port_b_out[3] ? sw[7:4] : sw[3:0];

wire ppi_control_access;





// PPI

KF8255 uF8255 (
    // Bus
    .clock(sys_clk),
    .reset(post_sdram_reset),
    .chip_select(ppi_control_access),
    
	 .read_enable (data_m_access & ~data_m_wr_en),
	 .write_enable(data_m_access & data_m_wr_en),
	 .ack(ppi_ack),
					 
    .address(data_m_addr[2:1]),

	 .data_bus_in(data_m_data_out[7:0]),
	 .data_bus_out(ppiout),
	 
	 // ack
	

    // I/O
    .port_a_in(keycode),
    //.[7:0]   port_a_out(),
    //.port_a_io(),

    //.[7:0]   port_b_in(),
    .port_b_out(port_b_out),
    //.port_b_io(),

    .port_c_in(port_c_in)
    //.[7:0]   port_c_out(),
    //.[7:0]   port_c_io()
);


// Cleaner RTL
AddressDecoderIO AddressDecoderIO(

    .d_io(d_io),
	 .data_m_addr(data_m_addr),
    .data_m_access(data_m_access),

    // Select outputs
    .leds_access(leds_access),
    .sdram_config_access(sdram_config_access),
    .default_io_access(default_io_access),
    .uart_access(uart_access),
	 .uart2_access(uart2_access),
    .irq_control_access(irq_control_access),
    .pic_access(pic_access),
    .timer_access(timer_access),
    .bios_control_access(bios_control_access),
    .mcga_reg_access(mcga_reg_access),
    .ps2_mouse_access(ps2_mouse_access),
	 .cga_reg_access(cga_reg_access),
	 .dma_page_chip_select(dma_page_chip_select),
	 .dma_chip_select(dma_chip_select),
	 .ppi_control_access(ppi_control_access)
	 .floppy_access(floppy_access)
	 
);











// proper decoding, no glitches, no delay

always_comb begin

    // Reset defaults
    sdram_access = 1'b0;
    bios_access  = 1'b0;
    mcga_access  = 1'b0;
	 cga_mem_access   = 1'b0;

    if (q_m_access) begin
          casez (q_m_addr[19:14])
              6'b111111: bios_access = 1'b1;
              //6'b101110, 6'b1010??: mcga_access = 1'b1; take me back
				  6'b110000, 6'b1010??: mcga_access = 1'b1; // Different non standar address C000
				  6'b101110: cga_mem_access = 1'b1;
              default:   sdram_access = 1'b1;
          endcase
		  
		  
    end
end

wire data_mem_ack;





// Instruction / Data Arbiter (CPU-only)
// Outputs to cpu_id_m_* which then goes to DMA arbiter

wire [19:1] cpu_id_m_addr;
wire [15:0] cpu_id_m_data_in;
wire [15:0] cpu_id_m_data_out;
wire cpu_id_m_access;
wire cpu_id_m_ack;
wire cpu_id_m_wr_en;
wire [1:0] cpu_id_m_bytesel;

IDArbiter IDArbiter(.clk(sys_clk),
                     .reset(post_sdram_reset),

                     .instr_m_addr(instr_m_addr),
                     .instr_m_data_in(instr_m_data_in),
                     .instr_m_data_out(16'b0),
                     .instr_m_access(instr_m_access),
                     .instr_m_ack(instr_m_ack),
                     .instr_m_wr_en(1'b0),
                     .instr_m_bytesel(2'b11),

                     .data_m_addr(data_m_addr),
                     .data_m_data_in(mem_data),
                     .data_m_data_out(data_m_data_out),
                     .data_m_access(data_m_access & ~d_io),
                     .data_m_ack(data_mem_ack),
                     .data_m_wr_en(data_m_wr_en),
                     .data_m_bytesel(data_m_bytesel),

                     // Output to DMA arbiter
                    .q_m_addr(cpu_id_m_addr),
                    .q_m_data_in(cpu_id_m_data_in),
                    .q_m_data_out(cpu_id_m_data_out),
                    .q_m_access(cpu_id_m_access),
                    .q_m_ack(cpu_id_m_ack),
                    .q_m_wr_en(cpu_id_m_wr_en),
                    .q_m_bytesel(cpu_id_m_bytesel),
                    .q_b());

// DMA Arbiter - Muxes CPU (instr+data) and DMA controller access to memory
// Priority: DMA has higher priority when active

// Prepare DMA data input (floppy write data when floppy DMA active)
assign dma_m_data_in[7:0] = (dma_acknowledge[2] & ~dma_m_wr_en) ? floppy_dma_writedata : 8'h00;
assign dma_m_data_in[15:8] = 8'h00;  // DMA transfers are 8-bit

DMAArbiter CPUDMAArbiter(
    .clk(sys_clk),
    .reset(post_sdram_reset),

    // DMA bus (higher priority)
    .a_m_addr(dma_m_addr),
    .a_m_data_in(dma_m_data_in),
    .a_m_data_out(dma_m_data_out),
    .a_m_access(dma_m_access & ~dma_d_io),  // Only memory access, not I/O
    .a_m_ack(dma_m_ack),
    .a_m_wr_en(dma_m_wr_en),
    .a_m_bytesel(dma_m_bytesel),
    .ioa(1'b0),  // DMA doesn't use I/O flag here

    // CPU (instruction + data) bus
    .b_m_addr(cpu_id_m_addr),
    .b_m_data_in(cpu_id_m_data_in),
    .b_m_data_out(cpu_id_m_data_out),
    .b_m_access(cpu_id_m_access),
    .b_m_ack(cpu_id_m_ack),
    .b_m_wr_en(cpu_id_m_wr_en),
    .b_m_bytesel(cpu_id_m_bytesel),
    .iob(1'b0),

    // Output to memory system (connects to CacheVGAArbiter)
    .q_m_addr(q_m_addr),
    .q_m_data_in(q_m_data_in),
    .q_m_data_out(q_m_data_out),
    .q_m_access(q_m_access),
    .q_m_ack(q_m_ack),
    .q_m_wr_en(q_m_wr_en),
    .q_m_bytesel(q_m_bytesel),
    .ioq(),
    .q_b()
);

// SDRAM<->Cache signals
wire [19:1] cache_sdram_m_addr;
wire [15:0] cache_sdram_m_data_in;
wire [15:0] cache_sdram_m_data_out;
wire cache_sdram_m_access;
wire cache_sdram_m_ack;
wire cache_sdram_m_wr_en;
wire [1:0] cache_sdram_m_bytesel;

// Low-level SDRAM signals
wire [19:1] sdram_m_addr;
wire [15:0] sdram_m_data_in;
wire [15:0] sdram_m_data_out;
wire sdram_m_access;
wire sdram_m_ack;
wire sdram_m_wr_en;
wire [1:0] sdram_m_bytesel;






// MemArbiter instantiation
// Comment and uncomment next block to connetc the 
// Direct Maped Cache (Combined Data / Instructions)



//MemArbiter CacheVGAArbiter(
MemArbiterExtend CacheVGAArbiter(
    .clk(sys_clk),
    .reset(post_sdram_reset),
	 

    // Connect CPU interface directly to the arbiter
    .cpu_m_addr(q_m_addr),
    .cpu_m_data_in(sdram_data),
    .cpu_m_data_out(q_m_data_out),
    .cpu_m_access(q_m_access & sdram_access),
    .cpu_m_ack(cache_ack),
    .cpu_m_wr_en(q_m_wr_en),
    .cpu_m_bytesel(q_m_bytesel),

    // VGA port
    .mcga_m_addr(fb_sdram_m_addr),
    .mcga_m_data_in(fb_sdram_m_data_in),
    .mcga_m_data_out(fb_sdram_m_data_out),
    .mcga_m_access(fb_sdram_m_access),
    .mcga_m_ack(fb_sdram_m_ack),
    .mcga_m_wr_en(fb_sdram_m_wr_en),
    .mcga_m_bytesel(fb_sdram_m_bytesel),

    // SDRAM interface
    .sdram_m_addr(sdram_m_addr),
    .sdram_m_data_in(sdram_m_data_out),
    .sdram_m_data_out(sdram_m_data_in),
    .sdram_m_access(sdram_m_access),
    .sdram_m_ack(sdram_m_ack),
    .sdram_m_wr_en(sdram_m_wr_en),
    .sdram_m_bytesel(sdram_m_bytesel),
    .q_b(arb_to_vga)
);


/*

Cache #(.lines(8192 / 16))
      Cache(
		
		      .enabled(1'b1),
		
            .clk(sys_clk),
				.reset(post_sdram_reset),
				
				
				// CPU interface
            .c_access(q_m_access & sdram_access),
            .c_addr(q_m_addr),
            .c_data_in(sdram_data),
            .c_data_out(q_m_data_out),
            .c_ack(cache_ack),
            .c_wr_en(q_m_wr_en),
            .c_bytesel(q_m_bytesel),
				
				
				// Memory interface
            .m_addr(cache_sdram_m_addr),
            .m_data_in(cache_sdram_m_data_out),
            .m_data_out(cache_sdram_m_data_in),
            .m_access(cache_sdram_m_access),
            .m_ack(cache_sdram_m_ack),
            .m_wr_en(cache_sdram_m_wr_en),
            .m_bytesel(cache_sdram_m_bytesel),
				
				
				
            );
				
MemArbiterExtend CacheVGAArbiter(.clk(sys_clk),
                           .reset(post_sdram_reset),
                           // Cache port
                           .cpu_m_addr(cache_sdram_m_addr),
                           .cpu_m_data_in(cache_sdram_m_data_out),
                           .cpu_m_data_out(cache_sdram_m_data_in),
                           .cpu_m_access(cache_sdram_m_access),
                           .cpu_m_ack(cache_sdram_m_ack),
                           .cpu_m_wr_en(cache_sdram_m_wr_en),
                           .cpu_m_bytesel(cache_sdram_m_bytesel),
						   
                           // VGA port
									
									
                           .mcga_m_addr(fb_sdram_m_addr),
                           .mcga_m_data_in(fb_sdram_m_data_in),
                           .mcga_m_data_out(fb_sdram_m_data_out),
                           .mcga_m_access(fb_sdram_m_access),
                           .mcga_m_ack(fb_sdram_m_ack),
                           .mcga_m_wr_en(fb_sdram_m_wr_en),
                           .mcga_m_bytesel(fb_sdram_m_bytesel),
									
									
						   
                           // Q
                           .sdram_m_addr(sdram_m_addr),
                           .sdram_m_data_in(sdram_m_data_out),
                           .sdram_m_data_out(sdram_m_data_in),
                           .sdram_m_access(sdram_m_access),
                           .sdram_m_ack(sdram_m_ack),
                           .sdram_m_wr_en(sdram_m_wr_en),
                           .sdram_m_bytesel(sdram_m_bytesel),
                           .q_b(arb_to_vga));
	

	*/
	
	
	
	

wire clk_mem;


pllsdram pllsdram
(
	.refclk(CLK_50M),
	.rst(0),
	.outclk_0(pllsdram1), // 80 MHz
	.outclk_1(pllsdram2), // 80 MHz
	.locked(plock)
);


// clock enable
assign SDRAM_CKE   = 1;

wire pllsdram2;
wire pllsdram1;


assign SDRAM_CLK = pllsdram2;

sdramtut6 SDRAM
(

   .clk     (pllsdram1   ),
	.init    (~plock      ),    // When pll is stable


	// CPU interface
	
	.oe		(sdram_m_access ),
	
	.we		(sdram_m_wr_en  ),
	.ack		(sdram_m_ack    ), // ack the operation

	.bytesel	(sdram_m_bytesel), // 16bit mode:  bit1 - write high byte, bit0 - write low byte,
                               // 8bit mode:  2'b00 - use addr[0] to decide which byte to write
                               // Ignored while reading.
											 
	.addr		({2'b0, arb_to_vga, sdram_m_addr}), // Arb_to_vga separates memory spaces
	.din	   (sdram_m_data_in ),
	.dout	   (sdram_m_data_out),
	

	// SDRAM signals
	
	.sd_data (SDRAM_DQ  	 ),   // 16 bit bidirectional data bus
	.sd_addr (SDRAM_A     ),   // 13 bit multiplexed address bus
	.sd_dqmh (SDRAM_DQMH),     // masks
	.sd_dqml (SDRAM_DQML),
	
	.sd_cs   (SDRAM_nCS   ),   // Chip select
	.sd_ba   (SDRAM_BA  	 ),   // Banks
	.sd_we   (SDRAM_nWE   ),   // write enable
	.sd_ras  (SDRAM_nRAS  ),   // row address select
	.sd_cas  (SDRAM_nCAS  ),   // columns address select
	
	

	// Other
	
	.configdone(sdram_config_done) // SDRAM was initialized
);

	


BIOS #(.depth(8192))
     BIOS(.clk(sys_clk),
          .cs(bios_access),
          .data_m_access(q_m_access),
          .data_m_ack(bios_ack),
          .data_m_addr(q_m_addr),
          .data_m_data_out(bios_data),
          .data_m_bytesel(q_m_bytesel),
          .data_m_data_in(q_m_data_out),
          .data_m_wr_en(q_m_wr_en));



								
   //input         UART_CTS,
	//output        UART_RTS,
	//output        UART_DTR,
	//input         UART_DSR,

wire uart1_tx;
wire rts_n;

MSMouseWrapper #(
    .CLKFREQ(30_000_000)  // Set the clock frequency to 30 MHz
) MSMouseWrapper_inst (
    .clk(sys_clk),
    .ps2dta_in (wps2_mouse_data_in), // Connect PS/2 data input
    .ps2clk_in (wps2_mouse_clk_in),  // Connect PS/2 clock input
    .ps2dta_out(wps2_mouse_data_out),// Connect PS/2 data output
    .ps2clk_out(wps2_mouse_clk_out), // Connect PS/2 clock output
    .rts(~rts_n),                    // Connect ready-to-send signal
    .rd(uart1_tx)                    // Connect read signal
);

wire clk_uart;


// Instantiate the uart module
uart uart_1 (
    .clk(sys_clk),
    .reset(post_sdram_reset),

    .address(data_m_addr[3:1]),            // UART address, 3 bits
	 .ack(uart1_ack),
    .write(data_m_wr_en & data_m_access), // Write enable signal
    .writedata(data_m_data_out[7:0]),     // Data to write, 8 bits
    .read(~data_m_wr_en & data_m_access),                 // Read enable signal
    .readdata(uart_data[7:0]),            // Data read, 8 bits
    .cs(uart_access),                     // Chip select for UART

    .br_clk(clk_uart),                    // Baud rate clock
    .rx(uart1_tx),                        // UART receive signal
    .tx(),                                // UART transmit signal
	 
	 
		  
    .cts_n(0),                        // Clear to send, active low
    .dcd_n(0),                        // Data carrier detect, active low
    .dsr_n(0),                        // Data set ready, active low
    .ri_n (1),                        // Ring indicator, active low
	 
    .rts_n(rts_n),                    // Request to send, active low
    .br_out(),                        // Baud rate output (optional, for external use)
    .dtr_n(),                         // Data terminal ready, active low

    .irq(uart1_interrupt)                   // Interrupt request output
);

wire uart2_tx, uart2_rts_n, uart2_dtr_n;

assign UART_TXD = uart2_tx;
assign UART_RTS = uart2_rts_n;
assign UART_DTR = uart2_dtr_n;

wire uart2_rx  = UART_RXD;
wire uart2_cts_n = UART_CTS;
wire uart2_dsr_n = UART_DSR;
wire uart2_dcd_n = UART_DTR;

wire uart1_interrupt;
wire uart2_interrupt;

uart uart_2 (
    .clk(sys_clk),
    .reset(post_sdram_reset),

    .address(data_m_addr[3:1]),           // UART address, 3 bits
    .write(data_m_wr_en & data_m_access), // Write enable signal
    .writedata(data_m_data_out[7:0]),     // Data to write, 8 bits
    .read(~data_m_wr_en & data_m_access), // Read enable signal
    .readdata(uart2_data[7:0]),           // Data read, 8 bits
    .cs(uart2_access),                    // Chip select for UART

	 .ack(uart2_ack),
    .br_clk(clk_uart),                    // Baud rate clock
    
	 
	 .rx                (uart2_rx),
    .tx                (uart2_tx),
	 
    .cts_n             (uart2_cts_n),     // Clear to send, active low
    .dcd_n             (uart2_dcd_n),
    .dsr_n             (uart2_dsr_n),
    .rts_n             (uart2_rts_n),     // Request to send, active low
    .dtr_n             (uart2_dtr_n),     // Data terminal ready, active low
		  
    
    
    .ri_n (1),                            // Ring indicator, active low
	 
    
    .br_out(),                            // Baud rate output (optional, for external use)
    

    .irq(uart2_interrupt)                 // Interrupt request output
);

													 

TriggerAfterNHigh #(
    .N(20)  // Set the N parameter for this instance
) triggerGenerator (
    .clk(sys_clk),           // Connect parent clk to TriggerAfterNHigh clk
    .rst(post_sdram_reset),           // Connect parent rst to TriggerAfterNHigh rst
    .signal_in(data_m_access), // Connect parent signal_in to TriggerAfterNHigh signal_in
    .trigger()    // Connect TriggerAfterNHigh trigger to parent trigger
);

		  
Core u80186(
    .clk(sys_clk),
    .reset(post_sdram_reset),

    // Interrupts
    .nmi(nmi),
    .intr(intr),
    .irq(irq),
    .inta(inta),

    // Instruction bus
    .instr_m_addr(instr_m_addr),
    .instr_m_data_in(instr_m_data_in),
    .instr_m_access(instr_m_access),
    .instr_m_ack(instr_m_ack),

    // Data bus
    .data_m_addr(data_m_addr),
    .data_m_data_in(data_m_data_in),
    .data_m_data_out(data_m_data_out),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .data_m_wr_en(data_m_wr_en),
    .data_m_bytesel(data_m_bytesel),
    .d_io(d_io), 
    .lock(),

    // Debug
    .debug_stopped(debug_stopped),
    .debug_seize(debug_seize),
    .debug_addr(debug_addr),
    .debug_run(debug_run),
    .debug_val(debug_val),
    .debug_wr_val(debug_wr_val),
    .debug_wr_en(debug_wr_en)
);


// Seems this module is used to test interrupts
// by generating interrupts with a port access 
// from CPU.

IRQController IRQController(.clk(sys_clk),
                            .reset(post_sdram_reset),
                            .cs(irq_control_access),
                            .data_m_ack(irq_control_ack),
                            .data_m_data_out(irq_control_data),
                            .data_m_data_in(data_m_data_out),
									 .nmi(nmi),
									 .intr_test(intr_test),
                            .*);


KF8259 PIC8259(

                .clk(sys_clk),
                .reset(post_sdram_reset),
					 
					 // Active low inputs modified
					 .chip_select (pic_access),
					 .read_enable (data_m_access & ~data_m_wr_en),
					 .write_enable(data_m_access & data_m_wr_en),
					 
					 .address(data_m_addr[1]),
					 
					 .data_bus_in(data_m_data_out),
					 .data_bus_out(pic_data),
					 .ack(pic_ack),

					 .interrupt_request(irqs),
					 
                //.interrupt_acknowledge_n(inta),
					 
					 .interrupt_acknowledge_n(1'b1),
					 
					 .data_bus_io(),
					 .simpleirq(irq),
					 .interrupt_to_cpu(intr),

					 //.cascade_out(),
					 //.cascade_io(),
					 
					 .cascade_in                 (3'b000),
					 .slave_program_n            (1'b1),
					 
					 .interrupt_acknowledge_simple(inta)

              );

wire dma_ack;
				  
wire dma_chip_select;
wire dma_page_chip_select;

wire fdd_dma_req;
wire [7:0] floppy_readdata;
wire [7:0] floppy_dma_writedata;
wire floppy_access;
wire floppy_ack;
wire [3:0] dma_acknowledge;
wire dma_terminal_count;

// DMA memory bus signals
wire [19:1] dma_m_addr;
wire [15:0] dma_m_data_in;
wire [15:0] dma_m_data_out;
wire dma_m_access;
wire dma_m_ack;
wire dma_m_wr_en;
wire [1:0] dma_m_bytesel;
wire dma_d_io;

DMAUnit uDMAUnit(

            .clk(sys_clk),
            .reset(post_sdram_reset),
				
				.dma_chip_select(dma_chip_select),
				.dma_page_chip_select(dma_page_chip_select),

				// CPU BUS (input)
				
				.cpu_ack(dma_ack),
				.m_cpu_data_in(data_m_data_out),
				.m_cpu_addr_in(data_m_addr),
				.m_cpu_access(data_m_access),
            .m_cpu_wr_en(data_m_wr_en),
				
				// DMA memory bus (to arbiter)
				.m_addr(dma_m_addr),
				.m_data_in(dma_m_data_in),
				.m_data_out(dma_m_data_out),
				.m_access(dma_m_access),
				.m_ack(dma_m_ack),
				.m_wr_en(dma_m_wr_en),
				.m_bytesel(dma_m_bytesel),
				.d_io(dma_d_io),

				// DMA device signals
				.dma_device_request({1'b0, fdd_dma_req, 1'b0, 1'b0}), // only floppy for now
				.dma_acknowledge(dma_acknowledge),
				.terminal_count(dma_terminal_count)

);


wire fdd_interrupt;

floppy floppy 
    (
        .clk                        (sys_clk),
        .reset                      (post_sdram_reset),

        //dma
        .dma_req                    (fdd_dma_req),
        .dma_ack                    (dma_acknowledge[2] & dma_m_ack),  // Floppy DMA channel 2 with memory ack
        .dma_tc                     (dma_terminal_count),              // Terminal count from DMA controller
        .dma_readdata               (dma_m_data_out[7:0]),             // DMA read data (memory -> floppy for write)
        .dma_writedata              (floppy_dma_writedata),            // DMA write data (floppy -> memory for read)

        //irq
        .irq                        (fdd_interrupt),

        //io buf
        .io_address                 (data_m_addr[3:1]),
        .io_read                    (floppy_access && !data_m_wr_en),
        .io_readdata                (floppy_readdata),
        .io_write                   (floppy_access && data_m_wr_en),
        .io_writedata               (data_m_data_out[7:0]),
        .bus_ack                    (floppy_ack),

        .fdd0_inserted              (/* not connected */),

        .mgmt_address               (4'b0),           // TODO: Connect to MiSTer SD interface
        .mgmt_fddn                  (1'b0),
        .mgmt_write                 (1'b0),
        .mgmt_writedata             (16'b0),
        .mgmt_read                  (1'b0),
        .mgmt_readdata              (/* not connected - TODO */),

        .wp                         (2'b00),          // Not write protected

        .clock_rate                 (28'd50_000_000),  // 50 MHz system clock

        .request                    (/* not connected - TODO: for SD card interface */)
    );
	 

Timer Timer(.clk(sys_clk),
            .reset(post_sdram_reset),
            .pit_clk(pit_clk),
            .cs(timer_access),
            .data_m_ack(timer_ack),
            .data_m_data_out(timer_data),
            .data_m_data_in(data_m_data_out),
            .data_m_addr(data_m_addr[2:1]),
            .intr(timer_intr),
            .speaker_out(`SPEAKER_TIMER_OUT),
            .speaker_gate_en(`SPEAKER_GATE_EN_IN),
            .*);


wire cursor_enabled;
wire graphics_enabled;
wire bright_colors;
wire palette_sel;
wire [3:0] background_color;
wire [14:0] cursor_pos;
wire [2:0] cursor_scan_start;
wire [2:0] cursor_scan_end;
wire vga_256_color;
wire [7:0] vga_dac_idx;
wire [17:0] vga_dac_rd;

wire [14:0] cpu_fb_addr = q_m_addr[19:16] == 4'ha ?
    q_m_addr[15:1] : {2'b0, q_m_addr[13:1]};

wire [15:0] fb_m_data;
wire [15:0] fb_address;
wire [15:0] fb_data;
wire fb_access;
wire fb_ack;

// SDRAM<->Cache signals
wire [19:1] fb_sdram_m_addr;
wire [15:0] fb_sdram_m_data_in;
wire [15:0] fb_sdram_m_data_out;
wire fb_sdram_m_access;
wire fb_sdram_m_ack;
wire fb_sdram_m_wr_en;
wire [1:0] fb_sdram_m_bytesel;
wire arb_to_vga;

//MemArbiter CPUVGAArbiter(.clk(sys_clk),
MemArbiterExtend CPUVGAArbiter(.clk(sys_clk),
                         .reset(post_sdram_reset),
                         // CPU port
                         .cpu_m_addr(cpu_fb_addr),
                         .cpu_m_data_in(vga_data),
                         .cpu_m_data_out(data_m_data_out),
                         .cpu_m_access(mcga_access),
                         .cpu_m_ack(vga_ack),
                         .cpu_m_wr_en(q_m_wr_en),
                         .cpu_m_bytesel(q_m_bytesel),
						 
                         // VGA port
                         .mcga_m_addr(fb_address),
                         .mcga_m_data_in(fb_data),
                         .mcga_m_data_out(),
                         .mcga_m_access(fb_access),
                         .mcga_m_ack(fb_ack),
                         .mcga_m_wr_en(1'b0),
                         .mcga_m_bytesel(2'b11),
						 
                         // Q
                         .sdram_m_addr(fb_sdram_m_addr),
                         .sdram_m_data_in(fb_sdram_m_data_in),
                         .sdram_m_data_out(fb_sdram_m_data_out),
                         .sdram_m_access(fb_sdram_m_access),
                         .sdram_m_ack(fb_sdram_m_ack),
                         .sdram_m_wr_en(fb_sdram_m_wr_en),
                         .sdram_m_bytesel(fb_sdram_m_bytesel),
                         .q_b());

								 							 


	

	
	wire vga_rw;
	wire vga_bw;
	wire vga_gw;
	
	
wire cga_mem_ack;
	
cgacard CGAVideoAdapter(

                   .clock(sys_clk),
                   .reset(post_sdram_reset),

						 .clk_vga_cga(vga_clk),

                   // VGA signals
		             .vga_hsync(HSync_AUX1),
		             .vga_vsync(VSync_AUX1),
		             .vga_r(VGA_R_AUX1[7:3]),
		             .vga_g(VGA_G_AUX1[7:3]),
		             .vga_b(VGA_B_AUX1[7:3]),
						 
						 
						 .H_BLANK(),
						 .V_BLANK(),
						 
						 .de_o_cga(VGA_DE_AUX1),
						 
						 .std_hsyncwidth(),
						 
						 
						 //output logic ce_pix,
						 
						 // Bus
                   
						 .regaccess(cga_reg_access),
                   .data_m_addr(data_m_addr),
                   .data_m_data_in(data_m_data_out),
                   .data_m_data_out(cga_reg_data),
                   .data_m_bytesel(data_m_bytesel),
                   .data_m_wr_en(data_m_wr_en),
                   .data_m_ack(cga_reg_ack),
						 
						 
						 
						 .memaccess(q_m_access & cga_mem_access),
						 .imem_m_addr(q_m_addr),
                   .imem_m_data_in(q_m_data_out),
                   .imem_m_data_out(cga_data),
                   .imem_m_bytesel(q_m_bytesel),
                   .imem_m_wr_en(q_m_wr_en),
                   .mem_m_ack(cga_mem_ack)

						 
                       );
							  
							  
									
VGAController VGAController(.clk(vga_clk),
                            .reset(post_sdram_reset),
                            
								
									 
									 .vga_r(VGA_R_AUX2[7:5]), // Map the 3 lower bits of vga_r to the 3 highest bits of VGA_R
                            .vga_g(VGA_G_AUX2[7:5]), // Map the 3 lower bits of vga_g to the 3 highest bits of VGA_G
                            .vga_b(VGA_B_AUX2[7:5]), // Map the 3 lower bits of vga_b to the 3 highest bits of VGA_B
									 .DE(VGA_DE_AUX2),
									 .vga_hsync(HSync_AUX2),
		                      .vga_vsync(VSync_AUX2),
									 
									 //.vga_r(), // Map the 3 lower bits of vga_r to the 3 highest bits of VGA_R
                            //.vga_g(), // Map the 3 lower bits of vga_g to the 3 highest bits of VGA_G
                            //.vga_b(), // Map the 3 lower bits of vga_b to the 3 highest bits of VGA_B
									 
									 //.DE(),
									 //.vga_hsync(),
		                      //.vga_vsync(),
									 
									 
									 .H_BLANK(),
									 .V_BLANK(),
									 .ce_pix(),
									 
									 
									 .vga_dac_idx(vga_dac_idx),
									 .vga_dac_rd(vga_dac_rd),
									 .cursor_pos(cursor_pos),
									 .cursor_scan_start(cursor_scan_start),
						          .cursor_scan_end(cursor_scan_end),
						          .vga_256_color(vga_256_color),
									 .bright_colors(bright_colors),
									 .palette_sel(palette_sel),
									 .background_color(background_color),
                            .*);
									 


//assign VGA_R = {vga_rw, 5'b00000}; // Assign the 4 bits of vga_r to the 4 highest bits of VGA_R and lower 4 bits to 0
//assign VGA_G = {vga_gw, 5'b00000}; // Assign the 4 bits of vga_g to the 4 highest bits of VGA_G and lower 4 bits to 0
//assign VGA_B = {vga_bw, 5'b00000}; // Assign the 4 bits of vga_b to the 4 highest bits of VGA_B and lower 4 bits to 0
									 

VGARegisters VGARegisters(.clk(sys_clk),
                          .reset(post_sdram_reset),
                          .cs(mcga_reg_access),
                          .data_m_ack(vga_reg_ack),
                          .data_m_data_out(vga_reg_data),
                          .data_m_data_in(data_m_data_out),
								  .vga_vsync(VSync),
								  .vga_hsync(HSync),
								  .cursor_pos(cursor_pos),
								  .cursor_scan_start(cursor_scan_start),
								  .cursor_scan_end(cursor_scan_end),
								  .vga_256_color(vga_256_color),
								  .bright_colors(bright_colors),
								  .palette_sel(palette_sel),
								  .background_color(background_color),
								  
								  
                          .*);
								  
								  
								  
								  
								  
// ---- Keyboard

logic   [7:0]   keycode_buf;
logic   [7:0]   keycode;

wire    clear_keycode = port_b_out[7];
wire    ps2_reset_n   = port_b_out[6];

logic   lock_recv_clock;

wire swap_video;
KFPS2KB u_KFPS2KB 
    (
        // Bus
        .clock                      (sys_clk),
        .peripheral_clock           (sys_clk),
        .reset                      (post_sdram_reset),

        // PS/2 I/O
        .device_clock               (wps2_kbd_clk_2 /*| lock_recv_clock*/),
        .device_data                (wps2_kbd_data_2),

        // I/O
        .irq                        (ps2_kbd_intr),
        .keycode                    (keycode_buf),
        .clear_keycode              (clear_keycode),
		  
        .pause_core                 (),
        .swap_video                 (swap_video),
        .video_output               (),
        .tandy_video                ()
    );

	 
	 
	 
    assign  keycode = ps2_reset_n ? keycode_buf : 8'h80;
	 logic   prev_ps2_reset_n;

	 always_ff @(posedge sys_clk or posedge post_sdram_reset)
    begin
        if (post_sdram_reset)
            prev_ps2_reset_n <= 1'b0;
        else
            prev_ps2_reset_n <= ps2_reset_n;
    end
	 
	 
	 
    // Sends Keyboard reset to PS2
	 // Still needs proper connection
    KFPS2KB_Send_Data u_KFPS2KB_Send_Data 
    (
        // Bus
        .clock                      (sys_clk),
        .peripheral_clock           (sys_clk),
        .reset                      (post_sdram_reset),

        // PS/2 I/O
        .device_clock               (wps2_kbd_clk_2),
        .device_clock_out           (wps2_kbd_clk_1),
        .device_data_out            (wps2_kbd_data_1),
		  
        .sending_data_flag          (lock_recv_clock),

        // I/O
        .send_request               (~prev_ps2_reset_n & ps2_reset_n),
        .send_data                  (8'hFF)
    );

	 


//assign CE_PIXEL = ce_pix;

//assign VGA_DE = ~(H_BLANK | V_BLANK);


assign VGA_HS = swap_video? HSync_AUX2 : HSync_AUX1;
assign VGA_VS = swap_video? VSync_AUX2 : VSync_AUX1;
assign CLK_VIDEO = vga_clk;
assign CE_PIXEL = 1;
assign VGA_R  =  swap_video ? VGA_R_AUX2   : VGA_R_AUX1;
assign VGA_G  =  swap_video ? VGA_G_AUX2   : VGA_G_AUX1;
assign VGA_B  =  swap_video ? VGA_B_AUX2   : VGA_B_AUX1;
assign VGA_DE  =  swap_video ? VGA_DE_AUX2 : VGA_DE_AUX1;


/*

assign VGA_R_AUX  =  swap_video & ~tandy_mode ? VGA_R_hgc  : VGA_R_cga;
    assign VGA_G_AUX  =  swap_video & ~tandy_mode ? VGA_G_hgc  : VGA_G_cga;
    assign VGA_B_AUX  =  swap_video & ~tandy_mode ? VGA_B_hgc  : VGA_B_cga;
    assign VGA_HS =  swap_video & ~tandy_mode ? VGA_HS_hgc : VGA_HS_cga;
    assign VGA_VS =  swap_video & ~tandy_mode ? VGA_VS_hgc : VGA_VS_cga;
    assign VGA_DE =  swap_video & ~tandy_mode ? VGA_DE_hgc : VGA_DE_cga;
    assign gamma_bus =  swap_video & ~tandy_mode ? gamma_bus_hgc : gamma_bus_cga;
    assign CE_PIXEL  =  swap_video & ~tandy_mode ? CE_PIXEL_hgc : CE_PIXEL_cga;
	 
	 */


/*
reg  [26:0] act_cnt;
always @(posedge clk_sys) act_cnt <= act_cnt + 1'd1; 
assign LED_USER    = act_cnt[26]  ? act_cnt[25:18]  > act_cnt[7:0]  : act_cnt[25:18]  <= act_cnt[7:0];

*/




wire leds_status;
wire wresetval;
						 
													 
LEDSRegister     LEDSRegister(.clk(sys_clk),
                              .cs(leds_access),
                              .leds_val(leds_status),
                              .data_m_data_in(data_m_data_out),
                              .data_m_data_out(leds_data),
                              .data_m_ack(leds_ack),
										.reset(post_sdram_reset),
										.resetval(wresetval),
                              .*);

// Counter for timing
reg [31:0] counter = 0;
reg blink_state = 0; // 0 for blink, 1 for pause

// Main logic
always @(posedge sys_clk) begin
    if (leds_status != 0) begin
        if (counter < (blink_state ? PAUSE_DURATION : BLINK_DURATION)) begin
            counter <= counter + 1;
        end else begin
            counter <= 0;
            blink_state <= ~blink_state; // Toggle state

            // At the end of the pause phase, reset leds_status
            if (blink_state) begin
                wresetval <= 0;
            end
        end

        if (!blink_state) begin
            // Blink logic
            LED_USER <= (counter % leds_status) == 0;
        end else begin
            // Pause logic
            LED_USER <= 0;
        end
    end else begin
        // If leds_status is 0, reset the blink state and counter
        blink_state <= 0;
        counter <= 0;
        LED_USER <= 0;
    end
end

	 

endmodule
