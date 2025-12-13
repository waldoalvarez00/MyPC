`timescale 1ns/1ns
//
// GameBoy Verilator Simulation Top-Level
//
// Wraps the GameBoy core for Verilator simulation with:
// - Clock generation (4MHz base, 8MHz double-speed)
// - ROM loading via ioctl interface (supports large ROMs with MBC)
// - SDRAM interface (exposed to C++ MisterSDRAMModel)
// - Video output (160x144 LCD)
// - Audio output
// - Input mapping
//

module top (
    input         clk_sys /*verilator public_flat*/,  // System clock (64MHz for SDRAM timing)
    input         reset /*verilator public_flat*/,
    input  [7:0]  inputs /*verilator public_flat*/,   // GameBoy buttons

    // Video output
    output [7:0]  VGA_R /*verilator public_flat*/,
    output [7:0]  VGA_G /*verilator public_flat*/,
    output [7:0]  VGA_B /*verilator public_flat*/,
    output        VGA_HS,
    output        VGA_VS,
    output        VGA_HB,
    output        VGA_VB,

    // Audio output
    output [15:0] AUDIO_L,
    output [15:0] AUDIO_R,

    // ROM loading interface (directly drives SDRAM for large ROMs)
    input         ioctl_download /*verilator public_flat*/,
    input         ioctl_wr /*verilator public_flat*/,
    input  [24:0] ioctl_addr /*verilator public_flat*/,
    input  [15:0] ioctl_dout /*verilator public_flat*/,  // 16-bit for SDRAM
    input  [7:0]  ioctl_index /*verilator public_flat*/,
    output        ioctl_wait /*verilator public_flat*/,

    // SDRAM interface - directly exposed to C++ model
    output [15:0] sd_data_out /*verilator public_flat*/,
    input  [15:0] sd_data_in /*verilator public_flat*/,
    output [12:0] sd_addr /*verilator public_flat*/,
    output [1:0]  sd_dqm /*verilator public_flat*/,
    output [1:0]  sd_ba /*verilator public_flat*/,
    output        sd_cs /*verilator public_flat*/,
    output        sd_we /*verilator public_flat*/,
    output        sd_ras /*verilator public_flat*/,
    output        sd_cas /*verilator public_flat*/,

    // Boot ROM download interface
    input         boot_download /*verilator public_flat*/,
    input         boot_wr /*verilator public_flat*/,
    input  [24:0] boot_addr /*verilator public_flat*/,
    input  [15:0] boot_data /*verilator public_flat*/,

    // Debug signals for diagnostics
    output        dbg_cart_rd /*verilator public_flat*/,
    output        dbg_cart_wr /*verilator public_flat*/,
    output        dbg_sdram_oe /*verilator public_flat*/,
    output        dbg_sdram_we /*verilator public_flat*/,
    output        dbg_dn_write /*verilator public_flat*/,
    output        dbg_ce_cpu /*verilator public_flat*/,
    output [1:0]  dbg_lcd_mode /*verilator public_flat*/,
    output [22:0] dbg_mbc_addr /*verilator public_flat*/,
    output        dbg_cart_ready /*verilator public_flat*/,
    output        dbg_cart_download /*verilator public_flat*/,
    output        dbg_boot_rom_enabled /*verilator public_flat*/,
    output        dbg_sel_boot_rom /*verilator public_flat*/,
    output [15:0] dbg_cpu_addr /*verilator public_flat*/,
    output        dbg_cpu_rd_n /*verilator public_flat*/,
    output        dbg_cpu_wr_n /*verilator public_flat*/,
    output        dbg_vram_wren /*verilator public_flat*/,
    output        dbg_vram_cpu_allow /*verilator public_flat*/,
    output        dbg_hdma_read_ext_bus /*verilator public_flat*/,
    output        dbg_dma_read_ext_bus /*verilator public_flat*/,
    output        dbg_hdma_active /*verilator public_flat*/,
    output        dbg_dma_rd /*verilator public_flat*/,
    output        dbg_cpu_clken /*verilator public_flat*/,
    output [7:0]  dbg_ie_r /*verilator public_flat*/,
    output [4:0]  dbg_if_r /*verilator public_flat*/,
    output        dbg_irq_n /*verilator public_flat*/,
    output        dbg_old_cpu_wr_n /*verilator public_flat*/,
    output        dbg_cpu_wr_n_edge /*verilator public_flat*/,
    output [23:0] dbg_sdram_addr /*verilator public_flat*/,
    output [1:0]  dbg_sdram_ds /*verilator public_flat*/,
    output [2:0]  dbg_sdram_state /*verilator public_flat*/,
    output        dbg_sdram_sync /*verilator public_flat*/,
    output        dbg_sdram_oe_pending /*verilator public_flat*/,
    output        dbg_sdram_we_pending /*verilator public_flat*/,
    output [15:0] dbg_sdram_dout_r /*verilator public_flat*/,
    output        dbg_sdram_oe_r /*verilator public_flat*/,
    output [15:0] dbg_sdram_do /*verilator public_flat*/,
    output [7:0]  dbg_rom_do /*verilator public_flat*/,
    output [7:0]  dbg_cart_do /*verilator public_flat*/,

    // Video debug signals
    output [7:0]  dbg_lcdc /*verilator public_flat*/,
    output        dbg_video_cpu_sel_reg /*verilator public_flat*/,
    output        dbg_video_cpu_wr /*verilator public_flat*/,
    output        dbg_lcd_on /*verilator public_flat*/,
    output        dbg_lcd_clkena /*verilator public_flat*/,
    output        dbg_lcd_vsync /*verilator public_flat*/,
    output [14:0] dbg_lcd_data /*verilator public_flat*/,
    output        dbg_isGBC_game /*verilator public_flat*/,
	    output [1:0]  dbg_lcd_data_gb /*verilator public_flat*/,
	    output        dbg_video_vram_rd /*verilator public_flat*/,
	    output [12:0] dbg_video_vram_addr /*verilator public_flat*/,
	    output [7:0]  dbg_video_vram_data /*verilator public_flat*/,
	    output [7:0]  dbg_video_vram1_data /*verilator public_flat*/,
		    output [1:0]  dbg_video_bg_pix_data /*verilator public_flat*/,
		    output [2:0]  dbg_video_bg_fetch_cycle /*verilator public_flat*/,
		    output [2:0]  dbg_video_bg_shift_cnt /*verilator public_flat*/,
		    output        dbg_video_bg_reload_shift /*verilator public_flat*/,
		    output        dbg_video_mode3 /*verilator public_flat*/,
		    output [7:0]  dbg_video_tile_shift_0 /*verilator public_flat*/,
		    output [7:0]  dbg_video_tile_shift_1 /*verilator public_flat*/,
		    output [7:0]  dbg_video_bgp /*verilator public_flat*/,
		    output [7:0]  dbg_video_scx /*verilator public_flat*/,
		    output [7:0]  dbg_video_scy /*verilator public_flat*/,
		    output [7:0]  dbg_video_ly /*verilator public_flat*/,
		    output [7:0]  dbg_cpu_do /*verilator public_flat*/,
		    output [7:0]  dbg_cpu_di /*verilator public_flat*/,
		    output [7:0]  dbg_boot_q /*verilator public_flat*/,
		    output [7:0]  dbg_boot_do /*verilator public_flat*/,
    output [15:0] dbg_cpu_tmpaddr /*verilator public_flat*/,
    output [7:0]  dbg_cpu_ir /*verilator public_flat*/,
    output [15:0] dbg_cpu_pc /*verilator public_flat*/,
	    output [15:0] dbg_cpu_sp /*verilator public_flat*/,
	    output [15:0] dbg_cpu_hl /*verilator public_flat*/,
	    output [15:0] dbg_cpu_de /*verilator public_flat*/,
	    output [15:0] dbg_cpu_bc /*verilator public_flat*/,
	    output [7:0]  dbg_cpu_acc /*verilator public_flat*/,
	    output [7:0]  dbg_cpu_f /*verilator public_flat*/,
	    output        dbg_cpu_write /*verilator public_flat*/,
	    output [6:0]  dbg_cpu_mcycle /*verilator public_flat*/,
	    output [6:0]  dbg_cpu_tstate /*verilator public_flat*/,
	    output [3:0]  dbg_cpu_set_busb_to /*verilator public_flat*/,
	    output [3:0]  dbg_cpu_set_busa_to /*verilator public_flat*/,
    output [2:0]  dbg_cpu_mcycles /*verilator public_flat*/,
    output [2:0]  dbg_cpu_mcycles_d /*verilator public_flat*/,

    // Extra CPU internal debug
    output        dbg_cpu_alternate /*verilator public_flat*/,
    output [15:0] dbg_cpu_hl_alt /*verilator public_flat*/,
    output [15:0] dbg_cpu_regbusc /*verilator public_flat*/,
    output [7:0]  dbg_cpu_di_latched /*verilator public_flat*/,
    output [4:0]  dbg_cpu_read_to_reg_r /*verilator public_flat*/,
    output        dbg_cpu_regweh /*verilator public_flat*/,
    output        dbg_cpu_regwel /*verilator public_flat*/,
    output [2:0]  dbg_cpu_regaddra /*verilator public_flat*/,
    output [1:0]  dbg_cpu_prefix /*verilator public_flat*/,
    output [1:0]  dbg_cpu_iset /*verilator public_flat*/
);

    // =========================================================================
    // Clock Generation
    // =========================================================================
    // GameBoy runs at 4.194304 MHz (normal) or 8.388608 MHz (GBC double-speed)
    // clk_sys should be 64MHz for proper SDRAM timing
    // Divide by 16 for ~4MHz ce, divide by 8 for ~8MHz ce_2x

    reg [3:0] clk_div;
    reg ce_cpu, ce_cpu_n, ce_cpu2x;

    // Wire for next clock divider value (used to fix clock enable timing)
    wire [3:0] clk_div_next = clk_div + 4'h1;

    // IMPORTANT: Clock enables must continue to run during reset!
    // The gb.v module uses ce (ce_cpu) to synchronize reset_r.
    // If ce_cpu is held at 0 during reset, reset_r never updates,
    // and the CPU never sees the reset signal.
    always @(posedge clk_sys) begin
        // Clock divider runs continuously (including during reset)
        clk_div <= clk_div_next;

        // CRITICAL FIX: Use incremented value for clock enables!
        // ce_cpu: ~4MHz enable (every 16 clocks at 64MHz)
        ce_cpu <= (clk_div_next == 4'h0);

        // ce_cpu_n: ~4MHz enable, opposite phase
        ce_cpu_n <= (clk_div_next == 4'h8);

        // ce_cpu2x: ~8MHz enable (every 8 clocks)
        ce_cpu2x <= (clk_div_next[2:0] == 3'h0);
    end

    // =========================================================================
    // SDRAM Controller
    // =========================================================================
    // Uses the MiSTer sdram controller, signals exposed to C++ model

    wire [22:0] mbc_addr;
    wire [15:0] sdram_do;
    wire [15:0] sdram_di;
    wire [23:0] sdram_addr;
    wire [1:0]  sdram_ds;
    wire        sdram_oe;
    wire        sdram_we;

    // Cart download detection
    wire cart_download = ioctl_download && (ioctl_index[5:0] == 6'h01 || ioctl_index == 8'h00 || ioctl_index == 8'h80);

    // SDRAM address: during download use ioctl_addr, during play use mbc_addr
    assign sdram_addr = cart_download ? ioctl_addr[24:1] : {1'b0, mbc_addr[22:1]};
    assign sdram_di = cart_download ? ioctl_dout : 16'd0;
    assign sdram_ds = cart_download ? 2'b11 : {mbc_addr[0], ~mbc_addr[0]};
    assign sdram_oe = ~cart_download & cart_rd & ~cram_rd;
    assign sdram_we = cart_download & dn_write;

    // Internal SDRAM signals for bidirectional data
    wire [15:0] sd_data_internal;

    sdram sdram_ctrl (
        // Interface to SDRAM chip (directly exposed to C++)
        .sd_data    (sd_data_internal),
        .sd_data_in (sd_data_in),      // Read data from C++ model
        .sd_addr    (sd_addr),
        .sd_dqm     (sd_dqm),
        .sd_ba      (sd_ba),
        .sd_cs      (sd_cs),
        .sd_we      (sd_we),
        .sd_ras     (sd_ras),
        .sd_cas     (sd_cas),
        .sd_clk     (),  // Not needed for simulation

        // System interface
        .clk        (clk_sys),
        // Drive the simplified SDRAM controller every clk_sys tick so that
        // SDRAM command sequencing (ACT/READ/WRITE/PRE) runs at the SDRAM clock
        // rate (64MHz) instead of the CPU clock enables (8MHz). With CAS=2 this
        // makes data ready well within a single CPU T-state, matching real hardware.
        .sync       (1'b1),
        .init       (reset),

        // CPU interface
        .din        (sdram_di),
        .addr       (sdram_addr),
        .ds         (sdram_ds),
        .we         (sdram_we),
        .oe         (sdram_oe),
        // The C++ Mister SDRAM model doesn't require refresh in simulation, and
        // periodic refresh bursts can delay back-to-back byte reads in ways the
        // fixed CPU WAIT_n window doesn't account for (shows up as stale opcode/imm bytes).
        .autorefresh(1'b0),
        .refresh    (1'b0),
        .dout       (sdram_do)
    );

    // SDRAM bidirectional handling for C++ interface
    assign sd_data_out = sd_data_internal;
    // Note: sd_data_in is fed back from C++ model, but for this controller
    // it's handled internally via sd_data tristate

    // ROM data from SDRAM
    wire [7:0] rom_do = mbc_addr[0] ? sdram_do[15:8] : sdram_do[7:0];

    // =========================================================================
    // Cartridge Interface with full MBC support
    // =========================================================================
    wire [14:0] cart_addr;
    wire        cart_a15;
    wire        cart_rd;
    wire        cart_wr;
    wire [7:0]  cart_do;
    wire [7:0]  cart_di;
    wire        cart_oe;
    wire        nCS;

    wire        dn_write;
    wire        cart_ready;
    wire        cram_rd, cram_wr;
    wire [7:0]  ram_mask_file, cart_ram_size;
    wire        isGBC_game, isSGB_game;
    wire        cart_has_save;
    wire [31:0] RTC_timestampOut;
    wire [47:0] RTC_savedtimeOut;
    wire        RTC_inuse;
    wire        rumbling;

    // 32kHz clock for RTC
    reg ce_32k;
    reg [10:0] ce_32k_div;
    always @(posedge clk_sys) begin
        ce_32k_div <= ce_32k_div + 1;
        ce_32k <= (ce_32k_div == 0);
    end

    cart_top cart (
        .reset          (reset),
        .clk_sys        (clk_sys),
        .ce_cpu         (ce_cpu),
        .ce_cpu2x       (ce_cpu2x),
        .speed          (speed),
        .megaduck       (1'b0),
        .mapper_sel     (3'b000),  // Auto-detect mapper

        .cart_addr      (cart_addr),
        .cart_a15       (cart_a15),
        .cart_rd        (cart_rd),
        .cart_wr        (cart_wr),
        .cart_do        (cart_do),
        .cart_di        (cart_di),
        .cart_oe        (cart_oe),
        .nCS            (nCS),

        .mbc_addr       (mbc_addr),
        .dn_write       (dn_write),
        .cart_ready     (cart_ready),

        .cram_rd        (cram_rd),
        .cram_wr        (cram_wr),

        .cart_download  (cart_download),
        .ram_mask_file  (ram_mask_file),
        .ram_size       (cart_ram_size),
        .has_save       (cart_has_save),

        .isGBC_game     (isGBC_game),
        .isSGB_game     (isSGB_game),

        .ioctl_download (ioctl_download),
        .ioctl_wr       (ioctl_wr),
        .ioctl_addr     (ioctl_addr),
        .ioctl_dout     (ioctl_dout),
        .ioctl_wait     (ioctl_wait),

        // Backup RAM (stubbed for now)
        .bk_wr          (1'b0),
        .bk_rtc_wr      (1'b0),
        .bk_addr        (17'h0),
        .bk_data        (16'h0),
        .bk_q           (),
        .img_size       (64'h0),

        .rom_di         (rom_do),

        .joystick_analog_0 (16'h0),

        .ce_32k         (ce_32k),
        .RTC_time       (33'h0),
        .RTC_timestampOut(RTC_timestampOut),
        .RTC_savedtimeOut(RTC_savedtimeOut),
        .RTC_inuse      (RTC_inuse),

        // Savestate interface (disabled)
        .SaveStateExt_Din  (64'h0),
        .SaveStateExt_Adr  (10'h0),
        .SaveStateExt_wren (1'b0),
        .SaveStateExt_rst  (1'b0),
        .SaveStateExt_Dout (),
        .savestate_load    (1'b0),
        .sleep_savestate   (1'b0),

        .Savestate_CRAMAddr     (20'h0),
        .Savestate_CRAMRWrEn    (1'b0),
        .Savestate_CRAMWriteData(8'h0),
        .Savestate_CRAMReadData (),

        .rumbling       (rumbling)
    );

    // =========================================================================
    // Input Mapping
    // =========================================================================
    // GameBoy button mapping:
    // Bit 0: Right, Bit 1: Left, Bit 2: Up, Bit 3: Down
    // Bit 4: A, Bit 5: B, Bit 6: Select, Bit 7: Start
    wire [7:0] joystick = inputs;

    // =========================================================================
    // Video Output
    // =========================================================================
    wire        lcd_clkena;
    wire [14:0] lcd_data;      // 5-bit R, 5-bit G, 5-bit B
    wire [1:0]  lcd_data_gb;
    wire [1:0]  lcd_mode;
    wire        lcd_on;
    wire        lcd_vsync;
    wire        vram_cpu_allow;

    // Convert DMG 2-bit monochrome to 8-bit grayscale
    // GameBoy DMG palette: 0=White, 1=Light gray, 2=Dark gray, 3=Black
    wire [7:0] dmg_gray;
    assign dmg_gray = (lcd_data_gb == 2'b00) ? 8'hFF :  // Color 0: White (#FFFFFF)
                      (lcd_data_gb == 2'b01) ? 8'hAA :  // Color 1: Light gray (#AAAAAA)
                      (lcd_data_gb == 2'b10) ? 8'h55 :  // Color 2: Dark gray (#555555)
                                               8'h00;   // Color 3: Black (#000000)

    // Convert 15-bit LCD data to 24-bit VGA (RGB555 -> RGB888 for GBC, grayscale for DMG)
    // Use isGBC_game to select between GBC color output and DMG monochrome output
    assign VGA_R = isGBC_game ? {lcd_data[14:10], lcd_data[14:12]} : dmg_gray;
    assign VGA_G = isGBC_game ? {lcd_data[9:5], lcd_data[9:7]} : dmg_gray;
    assign VGA_B = isGBC_game ? {lcd_data[4:0], lcd_data[4:2]} : dmg_gray;

    // Sync/blanking signals for the GUI rasterizer.
    //
    // The C++ SimVideo sink expects VGA-like level signals and detects line/frame
    // boundaries on falling edges. Use level (not 1-sysclk pulses) so edges are
    // observable when the GUI samples at the 4MHz CE rate.
    assign VGA_HS = (lcd_mode != 2'b00);  // low for entire HBlank
    assign VGA_VS = (lcd_mode != 2'b01);  // low for entire VBlank

    // Only present "active video" when the LCD pipeline asserts its pixel strobe.
    // Between CE ticks lcd_clkena is held, so the GUI must sample at CE.
    assign VGA_HB = ~lcd_clkena;
    assign VGA_VB = (lcd_mode == 2'b01);  // VBlank

    // =========================================================================
    // Audio Output
    // =========================================================================
    wire [15:0] audio_l, audio_r;
    assign AUDIO_L = audio_l;
    assign AUDIO_R = audio_r;

    // =========================================================================
    // Unused signals
    // =========================================================================
    wire [1:0] joy_p54;
    wire [3:0] joy_din = 4'hF;
    wire       speed;
    wire       DMA_on;
    wire       gg_available;
    wire       sc_int_clock2;
    wire       serial_clk_out;
    wire       serial_data_out;
    wire       sleep_savestate;

    // Savestate interface (stubbed)
    wire [63:0] SaveStateExt_Din;
    wire [9:0]  SaveStateExt_Adr;
    wire        SaveStateExt_wren;
    wire        SaveStateExt_rst;
    wire        SaveStateExt_load;
    wire [19:0] Savestate_CRAMAddr;
    wire        Savestate_CRAMRWrEn;
    wire [7:0]  Savestate_CRAMWriteData;
    wire [63:0] SAVE_out_Din;
    wire [63:0] SAVE_out_Dout;
    wire [25:0] SAVE_out_Adr;
    wire        SAVE_out_rnw;
    wire        SAVE_out_ena;
    wire [7:0]  SAVE_out_be;
    wire        SAVE_out_done;
    wire        rewind_active;

    // =========================================================================
    // GameBoy Core Instantiation
    // =========================================================================
    gb gameboy (
        .reset              (reset),
        .clk_sys            (clk_sys),
        .ce                 (ce_cpu),
        .ce_n               (ce_cpu_n),
        .ce_2x              (ce_cpu2x),

        .joystick           (joystick),
        .isGBC              (isGBC_game),  // Auto-detect from cart header
        .real_cgb_boot      (1'b0),
        .isSGB              (1'b0),
        .extra_spr_en       (1'b0),

        // Cartridge interface
        .ext_bus_addr       (cart_addr),
        .ext_bus_a15        (cart_a15),
        .cart_rd            (cart_rd),
        .cart_wr            (cart_wr),
        .cart_do            (cart_do),
        .cart_di            (cart_di),
        .cart_oe            (cart_oe),
        .nCS                (nCS),

        // Boot ROM downloads
        .cgb_boot_download  (1'b0),
        .dmg_boot_download  (boot_download),  // Use DMG boot (non-GBC games)
        .sgb_boot_download  (1'b0),
        .ioctl_wr           (boot_wr),
        .ioctl_addr         (boot_addr),
        .ioctl_dout         (boot_data),

        .boot_gba_en        (1'b0),
        .fast_boot_en       (1'b0),  // Full DMG boot (Nintendo logo + checks)

        // Audio
        .audio_l            (audio_l),
        .audio_r            (audio_r),
        .audio_no_pops      (1'b0),

        .megaduck           (1'b0),

        // LCD interface
        .lcd_clkena         (lcd_clkena),
        .lcd_data           (lcd_data),
        .lcd_data_gb        (lcd_data_gb),
        .lcd_mode           (lcd_mode),
        .lcd_on             (lcd_on),
        .lcd_vsync          (lcd_vsync),
        .vram_cpu_allow     (vram_cpu_allow),

        .joy_p54            (joy_p54),
        .joy_din            (joy_din),

        .speed              (speed),
        .DMA_on             (DMA_on),

        // Game Genie (disabled)
        .gg_reset           (1'b1),
        .gg_en              (1'b0),
        .gg_code            (129'h0),
        .gg_available       (gg_available),

        // Serial port (unused)
        .sc_int_clock2      (sc_int_clock2),
        .serial_clk_in      (1'b0),
        .serial_clk_out     (serial_clk_out),
        .serial_data_in     (1'b1),
        .serial_data_out    (serial_data_out),

        // Savestates (disabled)
        .increaseSSHeaderCount (1'b0),
        .cart_ram_size      (cart_ram_size),
        .save_state         (1'b0),
        .load_state         (1'b0),
        .savestate_number   (2'b00),
        .sleep_savestate    (sleep_savestate),

        .SaveStateExt_Din   (SaveStateExt_Din),
        .SaveStateExt_Adr   (SaveStateExt_Adr),
        .SaveStateExt_wren  (SaveStateExt_wren),
        .SaveStateExt_rst   (SaveStateExt_rst),
        .SaveStateExt_Dout  (64'h0),
        .SaveStateExt_load  (SaveStateExt_load),

        .Savestate_CRAMAddr     (Savestate_CRAMAddr),
        .Savestate_CRAMRWrEn    (Savestate_CRAMRWrEn),
        .Savestate_CRAMWriteData(Savestate_CRAMWriteData),
        .Savestate_CRAMReadData (8'h00),

        .SAVE_out_Din       (SAVE_out_Din),
        .SAVE_out_Dout      (SAVE_out_Dout),
        .SAVE_out_Adr       (SAVE_out_Adr),
        .SAVE_out_rnw       (SAVE_out_rnw),
        .SAVE_out_ena       (SAVE_out_ena),
        .SAVE_out_be        (SAVE_out_be),
        .SAVE_out_done      (SAVE_out_done),

        .rewind_on          (1'b0),
        .rewind_active      (rewind_active)
    );

    // =========================================================================
    // Debug Signal Assignments
    // =========================================================================
    assign dbg_cart_rd = cart_rd;
    assign dbg_cart_wr = cart_wr;
    assign dbg_sdram_oe = sdram_oe;
    assign dbg_sdram_we = sdram_we;
    assign dbg_sdram_addr = sdram_addr;
    assign dbg_sdram_ds = sdram_ds;
    assign dbg_sdram_state = sdram_ctrl.dbg_state;
    assign dbg_sdram_sync = ce_cpu2x;
    assign dbg_sdram_oe_pending = sdram_ctrl.dbg_oe_pending;
    assign dbg_sdram_we_pending = sdram_ctrl.dbg_we_pending;
    assign dbg_sdram_dout_r = sdram_ctrl.dbg_dout_r;
    assign dbg_sdram_oe_r = sdram_ctrl.dbg_oe_r;
    assign dbg_sdram_do = sdram_do;
    assign dbg_rom_do = rom_do;
    assign dbg_cart_do = cart_do;
    assign dbg_dn_write = dn_write;
    assign dbg_ce_cpu = ce_cpu;
    assign dbg_lcd_mode = lcd_mode;
    assign dbg_mbc_addr = mbc_addr;
    assign dbg_cart_ready = cart_ready;
    assign dbg_cart_download = cart_download;
    // Access internal gb signals via hierarchy for debugging
    assign dbg_boot_rom_enabled = gameboy.boot_rom_enabled;
    assign dbg_sel_boot_rom = gameboy.sel_boot_rom;
    assign dbg_cpu_addr = gameboy.cpu_addr;
    assign dbg_cpu_rd_n = gameboy.cpu_rd_n;
    assign dbg_cpu_wr_n = gameboy.cpu_wr_n;
    assign dbg_vram_wren = gameboy.vram_wren;
    assign dbg_vram_cpu_allow = gameboy.vram_cpu_allow;
    assign dbg_hdma_read_ext_bus = gameboy.hdma_read_ext_bus;
    assign dbg_dma_read_ext_bus = gameboy.dma_read_ext_bus;
    assign dbg_hdma_active = gameboy.hdma_active;
    assign dbg_dma_rd = gameboy.dma_rd;
    assign dbg_cpu_clken = gameboy.cpu_clken;
    assign dbg_ie_r = gameboy.ie_r;
    assign dbg_if_r = gameboy.if_r;
    assign dbg_irq_n = gameboy.irq_n;
    assign dbg_old_cpu_wr_n = gameboy.old_cpu_wr_n;
    assign dbg_cpu_wr_n_edge = gameboy.cpu_wr_n_edge;

    // Video debug assignments
    assign dbg_lcdc = gameboy.video.lcdc;
    assign dbg_video_cpu_sel_reg = gameboy.video.cpu_sel_reg;
    assign dbg_video_cpu_wr = gameboy.video.cpu_wr;
    assign dbg_lcd_on = lcd_on;
    assign dbg_lcd_clkena = lcd_clkena;
    assign dbg_lcd_vsync = lcd_vsync;
    assign dbg_lcd_data = lcd_data;
    assign dbg_isGBC_game = isGBC_game;
	    assign dbg_lcd_data_gb = lcd_data_gb;
	    assign dbg_video_vram_rd = gameboy.video.vram_rd;
	    assign dbg_video_vram_addr = gameboy.video.vram_addr;
	    assign dbg_video_vram_data = gameboy.video.vram_data;
	    assign dbg_video_vram1_data = gameboy.video.vram1_data;
	    assign dbg_video_bg_pix_data = gameboy.video.bg_pix_data;
    assign dbg_video_bg_fetch_cycle = gameboy.video.bg_fetch_cycle;
    assign dbg_video_bg_shift_cnt = gameboy.video.bg_shift_cnt;
    assign dbg_video_bg_reload_shift = gameboy.video.bg_reload_shift;
    assign dbg_video_mode3 = gameboy.video.mode3;
    assign dbg_video_tile_shift_0 = gameboy.video.tile_shift_0;
    assign dbg_video_tile_shift_1 = gameboy.video.tile_shift_1;
    assign dbg_video_bgp = gameboy.video.bgp;
    assign dbg_video_scx = gameboy.video.scx;
    assign dbg_video_scy = gameboy.video.scy;
    assign dbg_video_ly = gameboy.video.v_cnt;
	    assign dbg_cpu_do = gameboy.cpu_do;
	    assign dbg_cpu_di = gameboy.cpu_di;
	    assign dbg_boot_q = gameboy.boot_q;
	    assign dbg_boot_do = gameboy.boot_do;
    assign dbg_cpu_tmpaddr = gameboy.cpu.i_tv80_core.TmpAddr;
    assign dbg_cpu_ir = gameboy.cpu.i_tv80_core.IR;
	    assign dbg_cpu_pc = gameboy.cpu.i_tv80_core.PC;
	    assign dbg_cpu_sp = gameboy.cpu.i_tv80_core.SP;
	    assign dbg_cpu_hl = { gameboy.cpu.i_tv80_core.i_reg.RegsH[2], gameboy.cpu.i_tv80_core.i_reg.RegsL[2] };
	    assign dbg_cpu_de = { gameboy.cpu.i_tv80_core.i_reg.RegsH[1], gameboy.cpu.i_tv80_core.i_reg.RegsL[1] };
	    assign dbg_cpu_bc = { gameboy.cpu.i_tv80_core.i_reg.RegsH[0], gameboy.cpu.i_tv80_core.i_reg.RegsL[0] };
	    assign dbg_cpu_acc = gameboy.cpu.i_tv80_core.ACC;
	    assign dbg_cpu_f = gameboy.cpu.i_tv80_core.F;
	    assign dbg_cpu_write = gameboy.cpu.write;
	    assign dbg_cpu_mcycle = gameboy.cpu.mcycle;
	    assign dbg_cpu_tstate = gameboy.cpu.tstate;
	    assign dbg_cpu_set_busb_to = gameboy.cpu.i_tv80_core.Set_BusB_To;
	    assign dbg_cpu_set_busa_to = gameboy.cpu.i_tv80_core.Set_BusA_To;
    assign dbg_cpu_mcycles = gameboy.cpu.i_tv80_core.mcycles;
    assign dbg_cpu_mcycles_d = gameboy.cpu.i_tv80_core.mcycles_d;
    assign dbg_cpu_alternate = gameboy.cpu.i_tv80_core.Alternate;
    assign dbg_cpu_hl_alt = { gameboy.cpu.i_tv80_core.i_reg.RegsH[6], gameboy.cpu.i_tv80_core.i_reg.RegsL[6] };
    assign dbg_cpu_regbusc = gameboy.cpu.i_tv80_core.RegBusC;
    assign dbg_cpu_di_latched = gameboy.cpu.di_reg;
    assign dbg_cpu_read_to_reg_r = gameboy.cpu.i_tv80_core.Read_To_Reg_r;
    assign dbg_cpu_regweh = gameboy.cpu.i_tv80_core.RegWEH;
    assign dbg_cpu_regwel = gameboy.cpu.i_tv80_core.RegWEL;
    assign dbg_cpu_regaddra = gameboy.cpu.i_tv80_core.RegAddrA;
    assign dbg_cpu_prefix = gameboy.cpu.i_tv80_core.Prefix;
    assign dbg_cpu_iset = gameboy.cpu.i_tv80_core.ISet;

endmodule
