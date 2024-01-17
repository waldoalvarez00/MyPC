//============================================================================
//
//  Copyright Waldo Alvarez, 2023 
//  https://pipflow.com
//
//  This program is free software; you can redistribute it and/or modify it
//  under the terms of the GNU General Public License as published by the Free
//  Software Foundation; either version 2 of the License, or (at your option)
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

assign {UART_RTS, UART_DTR} = 0;

assign {SD_SCK, SD_MOSI, SD_CS} = 'Z;

//assign {SDRAM_DQ, SDRAM_A, SDRAM_BA, SDRAM_CLK, SDRAM_CKE, SDRAM_DQML, SDRAM_DQMH, SDRAM_nWE, SDRAM_nCAS, SDRAM_nRAS, SDRAM_nCS} = 'Z;
//assign {SDRAM_CKE, SDRAM_DQML, SDRAM_DQMH} = 'Z;

assign {DDRAM_CLK, DDRAM_BURSTCNT, DDRAM_ADDR, DDRAM_DIN, DDRAM_BE, DDRAM_RD, DDRAM_WE} = '0;  

assign VGA_SL = 0;
assign VGA_F1 = 0;
assign VGA_SCALER  = 0;
//assign VGA_DISABLE = 0;
//assign HDMI_FREEZE = 0;

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

`include "build_id.v" 
localparam CONF_STR = {
	"MyPC;;",
	"-;",
	"O[122:121],Aspect ratio,Original,Full Screen,[ARC1],[ARC2];",
	"O[2],TV Mode,NTSC,PAL;",
	"O[4:3],Noise,White,Red,Green,Blue;",
	"-;",
	"P1,Test Page 1;",
	"P1-;",
	"P1-, -= Options in page 1 =-;",
	"P1-;",
	"P1O[5],Option 1-1,Off,On;",
	"d0P1F1,BIN;",
	"H0P1O[10],Option 1-2,Off,On;",
	"-;",
	"P2,Test Page 2;",
	"P2-;",
	"P2-, -= Options in page 2 =-;",
	"P2-;",
	"P2S0,DSK;",
	"P2O[7:6],Option 2,1,2,3,4;",
	"-;",
	"-;",
	"T[0],Reset;",
	"R[0],Reset and close OSD;",
	"v,0;", // [optional] config version 0-99. 
	        // If CONF_STR options are changed in incompatible way, then change version number too,
			  // so all options will get default values on first start.
	"V,v",`BUILD_DATE 
};

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

hps_io #(.CONF_STR(CONF_STR)) hps_io
(
	.clk_sys(clk_sys),
	.HPS_BUS(HPS_BUS),
	.EXT_BUS(),
	.gamma_bus(),

	.forced_scandoubler(forced_scandoubler),

	.buttons(buttons),
	.status(status),
	.status_menumask({status[5]}),
	
	.ps2_key(ps2_key),
	
	
	
	
	// ps2 keyboard emulation
	.ps2_kbd_clk_out(wps2_kbd_clk_2),
	.ps2_kbd_data_out(wps2_kbd_data_2),
	.ps2_kbd_clk_in(wps2_kbd_clk_1),
	.ps2_kbd_data_in(wps2_kbd_data_1),

	//input       [2:0] ps2_kbd_led_status,
	//input       [2:0] ps2_kbd_led_use,

	.ps2_mouse_clk_out(wps2_mouse_clk_in),
	.ps2_mouse_data_out(wps2_mouse_data_in),
	.ps2_mouse_clk_in(wps2_mouse_clk_out),
	.ps2_mouse_data_in(wps2_mouse_data_out)
);

///////////////////////   CLOCKS   ///////////////////////////////

wire plock;
wire clk_sys;
wire vga_clk;


pll pll
(
	.refclk(CLK_50M),
	.rst(0),
	.outclk_0(clk_sys), // 30 MHz
	.outclk_1(vga_clk), // 25.11 MHz
	.outclk_2(pit_clk),
	// outclk_3 - used for signaltap II 150 MHz
	.outclk_4(clk_mem), // 120 MHz
	.locked(plock)
);




wire xreset = RESET; // | status[0] | buttons[1];

wire VSync;
wire HSync;














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

wire poweron_reset;
wire sys_clk;
wire reset_n;
wire pll_locked;



wire vga_reg_access;
wire vga_reg_ack;
wire [15:0] vga_reg_data;

wire vga_access;
wire vga_ack;
wire [15:0] vga_data;



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

wire [15:0] io_data = sdram_config_data |
    uart_data |
    spi_data |
    timer_data |
    irq_control_data |
    pic_data |

    vga_reg_data |


    ps2_kbd_data |
    ps2_mouse_data |

    leds_data |
    bios_control_data;
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

    vga_data |

    bios_data;
	 
	 
	 
wire q_m_ack = cache_ack |
    vga_ack |
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
wire bios_enabled;
wire [15:0] bios_control_data;

wire sdram_config_access;
wire sdram_config_ack;
wire sdram_config_done;
wire [15:0] sdram_config_data;


wire ps2_kbd_access;
wire ps2_kbd_ack;
wire [15:0] ps2_kbd_data;
wire ps2_kbd_intr;

wire ps2_mouse_access;
wire ps2_mouse_ack;
wire [15:0] ps2_mouse_data;
wire ps2_mouse_intr;


wire uart_access;
wire uart_ack;
wire [15:0] uart_data;

wire spi_access;
wire spi_ack;
wire [15:0] spi_data;

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
wire [15:0] pic_data;

wire [7:0] irqs = {ps2_mouse_intr, 5'b0, ps2_kbd_intr, timer_intr} | {1'b0, intr_test};

// Timer
wire pit_clk;
wire timer_intr;
wire timer_access;
wire timer_ack;
wire [15:0] timer_data;

wire default_io_access;
wire default_io_ack;

wire io_ack = sdram_config_ack |
              default_io_ack |
              uart_ack |
              leds_ack |
              spi_ack |
              irq_control_ack |
              pic_ack |
              timer_ack |

              vga_reg_ack |


              ps2_kbd_ack |
              ps2_mouse_ack |

              bios_control_ack;

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



always_ff @(posedge sys_clk)
    default_io_ack <= default_io_access;

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

always_comb begin
    sdram_access = 1'b0;
    bios_access = 1'b0;

    vga_access = 1'b0;


    if (q_m_access) begin
        unique casez ({bios_enabled, q_m_addr, 1'b0})
        {1'b1, 20'b1111_11??_????_????_????}: bios_access = 1'b1;

        {1'b?, 20'b1011_10??_????_????_????}: vga_access = 1'b1;
        {1'b?, 20'b1010_????_????_????_????}: vga_access = 1'b1;

        default: sdram_access = 1'b1;
        endcase
    end
end

wire data_mem_ack;

/*
BitSync         ResetSync(.clk(sys_clk),
                          .reset(1'b0),
                          .d(rst_in_n),
                          .q(reset_n));

*/

assign sys_clk = clk_sys;



// Instruction / Data Arbiter

MemArbiter IDArbiter(.clk(sys_clk),
                     .reset(xreset),

                     .a_m_addr(instr_m_addr),
                     .a_m_data_in(instr_m_data_in),
                     .a_m_data_out(16'b0),
                     .a_m_access(instr_m_access),
                     .a_m_ack(instr_m_ack),
                     .a_m_wr_en(1'b0),
                     .a_m_bytesel(2'b11),
							
							
                     .b_m_addr(data_m_addr),
                     .b_m_data_in(mem_data),
                     .b_m_data_out(data_m_data_out),
                     .b_m_access(data_m_access & ~d_io),
                     .b_m_ack(data_mem_ack),
                     .b_m_wr_en(data_m_wr_en),
                     .b_m_bytesel(data_m_bytesel),
							

                     // Output bus connections
                    .q_m_addr(q_m_addr),
                    .q_m_data_in(q_m_data_in),
                    .q_m_data_out(q_m_data_out),
                    .q_m_access(q_m_access),
                    .q_m_ack(q_m_ack),
                    .q_m_wr_en(q_m_wr_en),
                    .q_m_bytesel(q_m_bytesel),
                    .q_b());

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


/*
MemArbiter CacheVGAArbiter(
    .clk(sys_clk),
    .reset(xreset),
	 

    // Connect CPU interface directly to the arbiter
    .a_m_addr(q_m_addr),
    .a_m_data_in(sdram_data),
    .a_m_data_out(q_m_data_out),
    .a_m_access(q_m_access & sdram_access),
    .a_m_ack(cache_ack),
    .a_m_wr_en(q_m_wr_en),
    .a_m_bytesel(q_m_bytesel),

    // VGA port
    .b_m_addr(fb_sdram_m_addr),
    .b_m_data_in(fb_sdram_m_data_in),
    .b_m_data_out(fb_sdram_m_data_out),
    .b_m_access(fb_sdram_m_access),
    .b_m_ack(fb_sdram_m_ack),
    .b_m_wr_en(fb_sdram_m_wr_en),
    .b_m_bytesel(fb_sdram_m_bytesel),

    // SDRAM interface
    .q_m_addr(sdram_m_addr),
    .q_m_data_in(sdram_m_data_out),
    .q_m_data_out(sdram_m_data_in),
    .q_m_access(sdram_m_access),
    .q_m_ack(sdram_m_ack),
    .q_m_wr_en(sdram_m_wr_en),
    .q_m_bytesel(sdram_m_bytesel),
    .q_b(arb_to_vga)
);
*/


Cache #(.lines(8192 / 16))
      Cache(
		
		      .enabled(1'b1),
		
            .clk(sys_clk),
				.reset(xreset),
				
				
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
				
MemArbiter CacheVGAArbiter(.clk(sys_clk),
                           .reset(xreset),
                           // Cache port
                           .a_m_addr(cache_sdram_m_addr),
                           .a_m_data_in(cache_sdram_m_data_out),
                           .a_m_data_out(cache_sdram_m_data_in),
                           .a_m_access(cache_sdram_m_access),
                           .a_m_ack(cache_sdram_m_ack),
                           .a_m_wr_en(cache_sdram_m_wr_en),
                           .a_m_bytesel(cache_sdram_m_bytesel),
						   
                           // VGA port
									
									
                           .b_m_addr(fb_sdram_m_addr),
                           .b_m_data_in(fb_sdram_m_data_in),
                           .b_m_data_out(fb_sdram_m_data_out),
                           .b_m_access(fb_sdram_m_access),
                           .b_m_ack(fb_sdram_m_ack),
                           .b_m_wr_en(fb_sdram_m_wr_en),
                           .b_m_bytesel(fb_sdram_m_bytesel),
									
									
						   
                           // Q
                           .q_m_addr(sdram_m_addr),
                           .q_m_data_in(sdram_m_data_out),
                           .q_m_data_out(sdram_m_data_in),
                           .q_m_access(sdram_m_access),
                           .q_m_ack(sdram_m_ack),
                           .q_m_wr_en(sdram_m_wr_en),
                           .q_m_bytesel(sdram_m_bytesel),
                           .q_b(arb_to_vga));
	

	
	
	
	
	/*
sdram3g SDRAMController(

   .init(!plock),        // reset to initialize RAM
   .clk(sys_clk),
	
	
	                              // SDRAM_* - signals to the MT48LC16M16 chip
   .SDRAM_DQ(SDRAM_DQ),           // 16 bit bidirectional data bus
   .SDRAM_A(SDRAM_A),             // 13 bit multiplexed address bus
   .SDRAM_DQML(SDRAM_DQML),       // two byte masks
   .SDRAM_DQMH(SDRAM_DQMH),  
   .SDRAM_BA(SDRAM_BA),           // two banks
   .SDRAM_nCS(SDRAM_nCS),         // a single chip select
   .SDRAM_nWE(SDRAM_nWE),         // write enable
   .SDRAM_nRAS(SDRAM_nRAS),       // row address select
   .SDRAM_nCAS(SDRAM_nCAS),       // columns address select
   .SDRAM_CKE(SDRAM_CKE),         // clock enable
   .SDRAM_CLK(SDRAM_CLK),
                                  //
   .wtbt0(sdram_m_bytesel),        // 16bit mode:  bit1 - write high byte, bit0 - write low byte,
                                  // 8bit mode:  2'b00 - use addr[0] to decide which byte to write
                                  // Ignored while reading.
											 
	.addr0({5'b0, arb_to_vga, sdram_m_addr}),        // 25 bit address for 8bit mode. addr[0] = 0 for 16bit mode for correct operations.
   .dout0(sdram_m_data_out),                        // data output to cpu
   .din0(sdram_m_data_in),                          // data input from cpu
	
   //.we0(sdram_m_wr_en & sdram_m_access),            // cpu requests write
	
   .req0(~sdram_m_wr_en & sdram_m_access),           // cpu requests read
   
	.ack0(sdram_m_ack),                              // ack the operation
	
	
	.wrl0(sdram_m_bytesel[0]),
	.wrh0(sdram_m_bytesel[1]),
	
	.ready(),                                        // dout is valid. Ready to accept new read/write. (not connected)
	
	
	.configdone(sdram_config_done) // SDRAM was initialized

);*/

wire clk_mem;

sdrama4 SDRAM
(
	// CPU interface
	.wb_clk		(clk_sys		    ),
	.wb_req		(sdram_m_access ),
	
	.wb_we		(sdram_m_wr_en  ),
	.wb_ack		(sdram_m_ack    ),

	.wb_sel		(sdram_m_bytesel),
	.wb_adr		({2'b0, arb_to_vga, sdram_m_addr} ), // Arb_to_vga separates memory spaces
	.wb_dat_i	(sdram_m_data_in ),
	.wb_dat_o	(sdram_m_data_out),
	

	// SDRAM interface to the MT48LC16M16 chip
	.sd_clk_in	(clk_mem	 ),
	.sd_rst		(~plock	 ),

	.sd_clk_out (SDRAM_CLK   ),
	.sd_cke		(SDRAM_CKE	 ),
	.sd_dq   	(SDRAM_DQ  	 ),
	.sd_addr 	(SDRAM_A     ),
	//.sd_dqm     ({SDRAM_DQMH,SDRAM_DQML}),
	.sd_dqml     (SDRAM_DQML),
	.sd_dqmh     (SDRAM_DQMH),
	.sd_cs_n    (SDRAM_nCS   ),
	.sd_ba      (SDRAM_BA  	 ),
	.sd_we_n    (SDRAM_nWE   ),
	.sd_ras_n   (SDRAM_nRAS  ),
	.sd_cas_n   (SDRAM_nCAS  ),
	.sd_ready	( /*ram_ready*/ ),
	
	
	
	// Other
	
	.configdone(sdram_config_done) // SDRAM was initialized
);





	
/*

assign SDRAM_CLK = ~clk_sys;

sdram2cv SDRAMController
(
   .init(!plock),        // reset to initialize RAM
   .clk(sys_clk),
	
	
	                              // SDRAM_* - signals to the MT48LC16M16 chip
   .SDRAM_DQ(SDRAM_DQ),           // 16 bit bidirectional data bus
   .SDRAM_A(SDRAM_A),             // 13 bit multiplexed address bus
   .SDRAM_DQML(SDRAM_DQML),       // two byte masks
   .SDRAM_DQMH(SDRAM_DQMH),  
   .SDRAM_BA(SDRAM_BA),           // two banks
   .SDRAM_nCS(SDRAM_nCS),         // a single chip select
   .SDRAM_nWE(SDRAM_nWE),         // write enable
   .SDRAM_nRAS(SDRAM_nRAS),       // row address select
   .SDRAM_nCAS(SDRAM_nCAS),       // columns address select
   .SDRAM_CKE(SDRAM_CKE),         // clock enable
   //.SDRAM_CLK(SDRAM_CLK),
                                  //
   .wtbt(sdram_m_bytesel),        // 16bit mode:  bit1 - write high byte, bit0 - write low byte,
                                  // 8bit mode:  2'b00 - use addr[0] to decide which byte to write
                                  // Ignored while reading.
											 
	.addr({5'b0, arb_to_vga, sdram_m_addr}),        // 25 bit address for 8bit mode. addr[0] = 0 for 16bit mode for correct operations.
   .dout(sdram_m_data_out),                        // data output to cpu
   .din(sdram_m_data_in),                          // data input from cpu
   .we(sdram_m_wr_en & sdram_m_access),            // cpu requests write
   .rd(~sdram_m_wr_en & sdram_m_access),           // cpu requests read
   
	.ack(sdram_m_ack),                            // ack the operation
	
	.ready(),                            // dout is valid. Ready to accept new read/write.
	
	
	
	.configdone(sdram_config_done) // SDRAM was initialized
);

*/

	
	/*
	
sdram1 SDRAMController 
(
   .init(!plock),        // reset to initialize RAM
   .clk(sys_clk),
                                  //
                                  // SDRAM_* - signals to the MT48LC16M16 chip
   .SDRAM_DQ(SDRAM_DQ),           // 16 bit bidirectional data bus
   .SDRAM_A(SDRAM_A),             // 13 bit multiplexed address bus
   .SDRAM_DQML(SDRAM_DQML),       // two byte masks
   .SDRAM_DQMH(SDRAM_DQMH),  
   .SDRAM_BA(SDRAM_BA),           // two banks
   .SDRAM_nCS(SDRAM_nCS),         // a single chip select
   .SDRAM_nWE(SDRAM_nWE),         // write enable
   .SDRAM_nRAS(SDRAM_nRAS),       // row address select
   .SDRAM_nCAS(SDRAM_nCAS),       // columns address select
   .SDRAM_CKE(SDRAM_CKE),         // clock enable
   .SDRAM_CLK(SDRAM_CLK),
                                  //
   .wtbt(sdram_m_bytesel),        // 16bit mode:  bit1 - write high byte, bit0 - write low byte,
                                  // 8bit mode:  2'b00 - use addr[0] to decide which byte to write
                                  // Ignored while reading.
                                  //
   .addr({5'b0, arb_to_vga, sdram_m_addr}),        // 25 bit address for 8bit mode. addr[0] = 0 for 16bit mode for correct operations.
   .dout(sdram_m_data_out),                        // data output to cpu
   .din(sdram_m_data_in),                          // data input from cpu
   .we(sdram_m_wr_en & sdram_m_access),            // cpu requests write
   .rd(~sdram_m_wr_en & sdram_m_access),           // cpu requests read
   .ready(sdram_m_ack),                            // dout is valid. Ready to accept new read/write.
	
	
	
	.configdone(sdram_config_done) // SDRAM was initialized
);


*/
	
	
/*
SDRAMController #(.size(64 * 1024 * 1024),
                  .clkf(50000000))
                SDRAMController(.clk(sys_clk),
                                .reset(xreset),
                                .data_m_access(sdram_m_access),
                                .cs(1'b1),
                                .h_addr({5'b0, arb_to_vga, sdram_m_addr}),
                                .h_wdata(sdram_m_data_in),
                                .h_rdata(sdram_m_data_out),
                                .h_wr_en(sdram_m_wr_en),
                                .h_bytesel(sdram_m_bytesel),
                                .h_compl(sdram_m_ack),
                                .h_config_done(sdram_config_done),
										  
										  
										  
										  / * SDRAM signals. * /
                                .s_ras_n(SDRAM_nRAS),
                                .s_cas_n(SDRAM_nCAS),
                                .s_wr_en(SDRAM_nWE),
                                //.s_bytesel(),
                                .s_addr(SDRAM_A),
                                .s_cs_n(SDRAM_nCS),
                                .s_clken(SDRAM_CKE),
                                .s_data(SDRAM_DQ),
                                .s_banksel(SDRAM_BA)
										  
                                );*/

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

BIOSControlRegister BIOSControlRegister(.clk(sys_clk),
                                        .reset(xreset),
                                        .cs(bios_control_access),
                                        .data_m_ack(bios_control_ack),
                                        .data_m_data_out(bios_control_data),
                                        .bios_enabled(bios_enabled),
                                        .*);

SDRAMConfigRegister SDRAMConfigRegister(.clk(sys_clk),
                                        .cs(sdram_config_access),
                                        .data_m_ack(sdram_config_ack),
                                        .data_m_data_out(sdram_config_data),
                                        .config_done(sdram_config_done),
                                        .*);
												
										
								
   //input         UART_CTS,
	//output        UART_RTS,
	//output        UART_DTR,
	//input         UART_DSR,

	
													 
UartPorts #(.clk_freq(30000000))
          UartPorts(.clk(sys_clk),
                    .rx(UART_RXD),
                    .tx(UART_TXD),
                    .cs(uart_access),
                    .data_m_ack(uart_ack),
                    .data_m_data_out(uart_data),
                    .data_m_data_in(data_m_data_out),
						  .reset(xreset),
						  
                   
                   
                   .data_m_bytesel(data_m_bytesel),
                   .data_m_wr_en(data_m_wr_en),
                   .data_m_access(data_m_access));

						 

										
										/*



SPIPorts SPIPorts(.clk(sys_clk),
                  .cs(spi_access),
                  .data_m_ack(spi_ack),
                  .data_m_data_out(spi_data),
                  .data_m_data_in(data_m_data_out),
                  .data_m_addr(data_m_addr[1]),
                  .miso(spi_miso),
                  .mosi(spi_mosi),
                  .sclk(spi_sclk),
                  .ncs(spi_ncs),
                  .*);
						*/

						/*
`ifndef verilator
SysPLL	SysPLL(.refclk(clk),
	       .rst(1'b0),
               .locked(pll_locked),
               .*);
`endif // verilator

*/

		  
Core Core(
    .clk(sys_clk),
    .reset(xreset), // Replace with actual reset signal name

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

		  

IRQController IRQController(.clk(sys_clk),
                            .reset(xreset),
                            .cs(irq_control_access),
                            .data_m_ack(irq_control_ack),
                            .data_m_data_out(irq_control_data),
                            .data_m_data_in(data_m_data_out),
                            .*);

PIC PIC(.clk(sys_clk),
        .reset(xreset),
        .cs(pic_access),
        .data_m_ack(pic_ack),
        .data_m_data_out(pic_data),
        .data_m_data_in(data_m_data_out),
        .intr_in(irqs),
        .*);

Timer Timer(.clk(sys_clk),
            .reset(xreset),
            .pit_clk(pit_clk),
            .cs(timer_access),
            .data_m_ack(timer_ack),
            .data_m_data_out(timer_data),
            .data_m_data_in(data_m_data_out),
            .data_m_addr(data_m_addr[1]),
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

MemArbiter CPUVGAArbiter(.clk(sys_clk),
                         .reset(xreset),
                         // CPU port
                         .a_m_addr(cpu_fb_addr),
                         .a_m_data_in(vga_data),
                         .a_m_data_out(data_m_data_out),
                         .a_m_access(vga_access),
                         .a_m_ack(vga_ack),
                         .a_m_wr_en(q_m_wr_en),
                         .a_m_bytesel(q_m_bytesel),
						 
                         // VGA port
                         .b_m_addr(fb_address),
                         .b_m_data_in(fb_data),
                         .b_m_data_out(),
                         .b_m_access(fb_access),
                         .b_m_ack(fb_ack),
                         .b_m_wr_en(1'b0),
                         .b_m_bytesel(2'b11),
						 
                         // Q
                         .q_m_addr(fb_sdram_m_addr),
                         .q_m_data_in(fb_sdram_m_data_in),
                         .q_m_data_out(fb_sdram_m_data_out),
                         .q_m_access(fb_sdram_m_access),
                         .q_m_ack(fb_sdram_m_ack),
                         .q_m_wr_en(fb_sdram_m_wr_en),
                         .q_m_bytesel(fb_sdram_m_bytesel),
                         .q_b());

								 							 


	
	
	//wire H_BLANK;
	//wire V_BLANK;
	//wire ce_pix;
	
	
									
VGAController VGAController(.clk(vga_clk),
                            .reset(xreset),
                            .vga_r(VGA_R[7:5]), // Map the 3 lower bits of vga_r to the 3 highest bits of VGA_R
                            .vga_g(VGA_G[7:5]), // Map the 3 lower bits of vga_g to the 3 highest bits of VGA_G
                            .vga_b(VGA_B[7:5]), // Map the 3 lower bits of vga_b to the 3 highest bits of VGA_B
									 .vga_hsync(HSync),
		                      .vga_vsync(VSync),
									 .H_BLANK(/*H_BLANK*/),
									 .V_BLANK(/*V_BLANK*/),
									 .ce_pix(/*ce_pix*/),
									 .DE(VGA_DE),
                            .*);

VGARegisters VGARegisters(.clk(sys_clk),
                          .reset(xreset),
                          .cs(vga_reg_access),
                          .data_m_ack(vga_reg_ack),
                          .data_m_data_out(vga_reg_data),
                          .data_m_data_in(data_m_data_out),
								  .vga_vsync(VSync),
								  .vga_hsync(HSync),
                          .*);

								  


PS2KeyboardController #(.clkf(50000000))
		      PS2KeyboardController(.clk(sys_clk),
				       .reset(xreset),
					    .cs(ps2_kbd_access),
					    .data_m_ack(ps2_kbd_ack),
					    .data_m_data_out(ps2_kbd_data),
					    .data_m_data_in(data_m_data_out),
                                            .ps2_intr(ps2_kbd_intr),
                                            .speaker_gate_en(`SPEAKER_GATE_EN_OUT),
                                            .speaker_data(`SPEAKER_DATA),
														  
														  .ps2_clk_in(wps2_kbd_clk_2),
					                             .ps2_clk_out(wps2_kbd_clk_1),
					                             .ps2_dat_in(wps2_kbd_data_2),
					                             .ps2_dat_out(wps2_kbd_data_1),
					    .*);

				
	

PS2MouseController #(.clkf(50000000))
		   PS2MouseController(.clk(sys_clk),
			                             .reset(xreset),
                                      .cs(ps2_mouse_access),
                                      .data_m_ack(ps2_mouse_ack),
                                      .data_m_data_out(ps2_mouse_data),
                                      .data_m_data_in(data_m_data_out),
                                      .ps2_intr(ps2_mouse_intr),
												  
                                      //.ps2_clk(ps2_clk_b),
                                      //.ps2_dat(ps2_dat_b),
												  
												  .ps2_clk_in(wps2_mouse_clk_in),
					                       .ps2_clk_out(wps2_mouse_clk_out),
					                       .ps2_dat_in(wps2_mouse_data_in),
					                       .ps2_dat_out(wps2_mouse_data_out),
									
                                      .*);


												  /*
PoweronReset PoweronReset(.*);
*/






//assign CE_PIXEL = ce_pix;


	

//assign VGA_DE = ~(H_BLANK | V_BLANK);
assign VGA_HS = HSync;
assign VGA_VS = VSync;
assign CLK_VIDEO = vga_clk;
assign CE_PIXEL = 1;

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
										.reset(xreset),
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