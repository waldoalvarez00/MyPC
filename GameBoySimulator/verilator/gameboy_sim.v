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
    output        sd_cas /*verilator public_flat*/
);

    // =========================================================================
    // Clock Generation
    // =========================================================================
    // GameBoy runs at 4.194304 MHz (normal) or 8.388608 MHz (GBC double-speed)
    // clk_sys should be 64MHz for proper SDRAM timing
    // Divide by 16 for ~4MHz ce, divide by 8 for ~8MHz ce_2x

    reg [3:0] clk_div;
    reg ce_cpu, ce_cpu_n, ce_cpu2x;

    always @(posedge clk_sys) begin
        if (reset) begin
            clk_div <= 0;
            ce_cpu <= 0;
            ce_cpu_n <= 0;
            ce_cpu2x <= 0;
        end else begin
            clk_div <= clk_div + 1;

            // ce_cpu: ~4MHz enable (every 16 clocks at 64MHz)
            ce_cpu <= (clk_div == 4'h0);

            // ce_cpu_n: ~4MHz enable, opposite phase
            ce_cpu_n <= (clk_div == 4'h8);

            // ce_cpu2x: ~8MHz enable (every 8 clocks)
            ce_cpu2x <= (clk_div[2:0] == 3'h0);
        end
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
        .sync       (ce_cpu2x),
        .init       (reset),

        // CPU interface
        .din        (sdram_di),
        .addr       (sdram_addr),
        .ds         (sdram_ds),
        .we         (sdram_we),
        .oe         (sdram_oe),
        .autorefresh(1'b1),
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

    // Convert 15-bit LCD data to 24-bit VGA (RGB555 -> RGB888)
    assign VGA_R = {lcd_data[14:10], lcd_data[14:12]};
    assign VGA_G = {lcd_data[9:5], lcd_data[9:7]};
    assign VGA_B = {lcd_data[4:0], lcd_data[4:2]};

    // Sync signals from LCD mode
    assign VGA_HS = 1'b1;
    assign VGA_VS = ~lcd_vsync;
    assign VGA_HB = (lcd_mode == 2'b00);  // HBlank
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

        // Boot ROM downloads (none for simulation)
        .cgb_boot_download  (1'b0),
        .dmg_boot_download  (1'b0),
        .sgb_boot_download  (1'b0),
        .ioctl_wr           (1'b0),
        .ioctl_addr         (25'h0),
        .ioctl_dout         (16'h0),

        .boot_gba_en        (1'b0),
        .fast_boot_en       (1'b1),  // Enable fast boot

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

endmodule
