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

assign {UART_RTS, UART_DTR} = 0;

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

hps_io #(.CONF_STR(CONF_STR), .PS2DIV(2000), .PS2WE(1)) hps_io
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
	.locked(/*plock*/)
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
				  
				  
reg post_sdram_reset; // delayed reset after SDRAM is configured

always @(posedge sys_clk or posedge xreset) begin
    if (xreset) begin
        // When system is under reset, prepare to wait for SDRAM configuration
        post_sdram_reset <= 1'b1;
    end else if (sdram_config_done) begin
        // Once SDRAM configuration is done, clear the post SDRAM reset signal
        post_sdram_reset <= 1'b0;
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
always_ff @(posedge sys_clk)
    default_io_ack <= default_io_access;

	 
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
    .spi_access(spi_access),
    .irq_control_access(irq_control_access),
    .pic_access(pic_access),
    .timer_access(timer_access),
    .bios_control_access(bios_control_access),
    .vga_reg_access(vga_reg_access),
    .ps2_kbd_access(ps2_kbd_access),
    .ps2_mouse_access(ps2_mouse_access)
	 
);




/*

// original

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

*/





/*



always_comb begin
    // Default assignments
    sdram_access = 1'b0;
    bios_access = 1'b0;
    vga_access = 1'b0;

    // Determine access type based on conditions
    if (q_m_access) begin
        // Check for BIOS access
        if (bios_enabled && q_m_addr[19:14] == 8'b1111_11) begin
            bios_access = 1'b1;
        end
        // Check for VGA access
        else if (q_m_addr[19:14] == 6'b1011_10 || q_m_addr[19:16] == 4'b1010) begin
            vga_access = 1'b1;
        end
        // Default to SDRAM access
        else begin
            sdram_access = 1'b1;
        end
    end
    
end

*/


// proper decoding, no glitches, no delay

always_comb begin
    // Reset defaults
    sdram_access = 1'b0;
    bios_access = 1'b0;
    vga_access = 1'b0;

    if (q_m_access) begin
	    if(bios_enabled) begin
          casez (q_m_addr[19:14])
              6'b111111: bios_access = 1'b1;
              6'b101110, 6'b1011??: vga_access = 1'b1;
              default:   sdram_access = 1'b1;
          endcase
		  end else begin
		    casez (q_m_addr[19:14])
			     // BIOS Turns into RAM
              6'b101110: vga_access   = 1'b1;
				  6'b1011??: vga_access   = 1'b1;
              default:   sdram_access = 1'b1;
        endcase
		  end
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

IDArbiter IDArbiter(.clk(sys_clk),
//MemArbiter IDArbiter(.clk(sys_clk),
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
							//.data_m_ack(extendw),
                     .data_m_wr_en(data_m_wr_en),
                     .data_m_bytesel(data_m_bytesel),
							

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



//MemArbiter CacheVGAArbiter(
MemArbiterExtend CacheVGAArbiter(
    .clk(sys_clk),
    .reset(post_sdram_reset),
	 

    // Connect CPU interface directly to the arbiter
    .cpu_m_addr(q_m_addr),
    .cpu_m_data_in(sdram_data),
    .cpu_m_data_out(q_m_data_out),
    .cpu_m_access(/*q_m_access &*/ sdram_access), // q_m_access seems an attempt to eliminate a glitch in sdram_access
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
				.reset(xreset),
				
				
				// CPU interface
            .c_access(/*q_m_access &* / sdram_access),
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
                           .reset(xreset),
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
                                        .reset(post_sdram_reset),
                                        .cs(bios_control_access),
                                        .data_m_ack(bios_control_ack),
                                        .data_m_data_out(bios_control_data),
                                        .bios_enabled(bios_enabled),
                                        .*);


													 
													 
// CPU can read this port to check if SDRAM was initialized

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
						  .reset(post_sdram_reset),
						  
                   
                   
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

		  
Core u80186(
    .clk(sys_clk),
    .reset(post_sdram_reset), // Replace with actual reset signal name

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



PIC PIC(.clk(sys_clk),
        .reset(post_sdram_reset),
        .cs(pic_access),
        .data_m_ack(pic_ack),
        .data_m_data_out(pic_data),
        .data_m_data_in(data_m_data_out),
        .intr_in(irqs),
        .*);



Timer Timer(.clk(sys_clk),
            .reset(post_sdram_reset),
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

//MemArbiter CPUVGAArbiter(.clk(sys_clk),
MemArbiterExtend CPUVGAArbiter(.clk(sys_clk),
                         .reset(post_sdram_reset),
                         // CPU port
                         .cpu_m_addr(cpu_fb_addr),
                         .cpu_m_data_in(vga_data),
                         .cpu_m_data_out(data_m_data_out),
                         .cpu_m_access(vga_access),
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

								 							 


	
	
	//wire H_BLANK;
	//wire V_BLANK;
	//wire ce_pix;
	
	wire vga_rw;
	wire vga_bw;
	wire vga_gw;
	
									
VGAController VGAController(.clk(vga_clk),
                            .reset(post_sdram_reset),
                            
									 //.vga_r(vga_rw),
                            //.vga_g(vga_gw),
                            //.vga_b(vga_bw),
									 
									 .vga_r(VGA_R[7:5]), // Map the 3 lower bits of vga_r to the 3 highest bits of VGA_R
                            .vga_g(VGA_G[7:5]), // Map the 3 lower bits of vga_g to the 3 highest bits of VGA_G
                            .vga_b(VGA_B[7:5]), // Map the 3 lower bits of vga_b to the 3 highest bits of VGA_B
									 
									 .vga_hsync(HSync),
		                      .vga_vsync(VSync),
									 .H_BLANK(),
									 .V_BLANK(),
									 .ce_pix(),
									 .DE(VGA_DE),
                            .*);
									 


//assign VGA_R = {vga_rw, 5'b00000}; // Assign the 4 bits of vga_r to the 4 highest bits of VGA_R and lower 4 bits to 0
//assign VGA_G = {vga_gw, 5'b00000}; // Assign the 4 bits of vga_g to the 4 highest bits of VGA_G and lower 4 bits to 0
//assign VGA_B = {vga_bw, 5'b00000}; // Assign the 4 bits of vga_b to the 4 highest bits of VGA_B and lower 4 bits to 0
									 

VGARegisters VGARegisters(.clk(sys_clk),
                          .reset(post_sdram_reset),
                          .cs(vga_reg_access),
                          .data_m_ack(vga_reg_ack),
                          .data_m_data_out(vga_reg_data),
                          .data_m_data_in(data_m_data_out),
								  .vga_vsync(VSync),
								  .vga_hsync(HSync),
                          .*);

								  


PS2KeyboardController #(.clkf(50000000))
		      PS2KeyboardController(.clk(sys_clk),
				       .reset(post_sdram_reset),
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
			                             .reset(post_sdram_reset),
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
