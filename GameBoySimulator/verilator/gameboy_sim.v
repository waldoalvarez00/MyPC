`timescale 1ns/1ns
//
// GameBoy Verilator Simulation Top-Level
//
// Wraps the GameBoy core for Verilator simulation with:
// - Clock generation (4MHz base, 8MHz double-speed)
// - ROM loading via ioctl interface
// - Video output (160x144 LCD)
// - Audio output
// - Input mapping
//

module top (
    input         clk_sys /*verilator public_flat*/,  // System clock (e.g., 32MHz or 64MHz)
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

    // ROM loading interface
    input         ioctl_download,
    input         ioctl_upload,
    input         ioctl_wr,
    input  [24:0] ioctl_addr,
    input  [7:0]  ioctl_dout,
    output [7:0]  ioctl_din,
    input  [7:0]  ioctl_index,
    output reg    ioctl_wait = 1'b0
);

    // =========================================================================
    // Clock Generation
    // =========================================================================
    // GameBoy runs at 4.194304 MHz (normal) or 8.388608 MHz (GBC double-speed)
    // We'll use a clock divider from clk_sys

    reg [3:0] clk_div;
    reg ce, ce_n, ce_2x;

    // Assuming clk_sys is 32MHz, divide by 8 for ~4MHz
    // Adjust CLK_DIV_RATIO based on your actual clk_sys frequency
    localparam CLK_DIV_RATIO = 8;

    always @(posedge clk_sys) begin
        if (reset) begin
            clk_div <= 0;
            ce <= 0;
            ce_n <= 0;
            ce_2x <= 0;
        end else begin
            clk_div <= clk_div + 1;

            // ce: 4MHz enable (every 8 clocks)
            ce <= (clk_div == 0);

            // ce_n: 4MHz enable, opposite phase
            ce_n <= (clk_div == (CLK_DIV_RATIO/2));

            // ce_2x: 8MHz enable (every 4 clocks)
            ce_2x <= (clk_div[2:0] == 0) || (clk_div[2:0] == 4);
        end
    end

    // =========================================================================
    // Cartridge Interface (Simple ROM simulation)
    // =========================================================================
    wire [14:0] ext_bus_addr;
    wire        ext_bus_a15;
    wire        cart_rd;
    wire        cart_wr;
    wire [7:0]  cart_di;
    reg  [7:0]  cart_do;
    wire        cart_oe;
    wire        nCS;

    // Simple ROM (32KB for testing)
    reg [7:0] rom [0:32767];
    wire [15:0] rom_addr = {ext_bus_a15, ext_bus_addr};

    // Load ROM via ioctl
    always @(posedge clk_sys) begin
        if (ioctl_download && ioctl_wr && ioctl_index == 8'h00) begin
            if (ioctl_addr < 32768)
                rom[ioctl_addr[14:0]] <= ioctl_dout;
        end
    end

    // ROM read
    always @(posedge clk_sys) begin
        if (cart_rd)
            cart_do <= rom[rom_addr[14:0]];
    end

    // =========================================================================
    // Input Mapping
    // =========================================================================
    // GameBoy button mapping:
    // Bit 0: Right
    // Bit 1: Left
    // Bit 2: Up
    // Bit 3: Down
    // Bit 4: A
    // Bit 5: B
    // Bit 6: Select
    // Bit 7: Start
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

    // Convert 15-bit LCD data to 24-bit VGA
    // lcd_data is RGB555
    assign VGA_R = {lcd_data[14:10], lcd_data[14:12]};  // Expand 5-bit to 8-bit
    assign VGA_G = {lcd_data[9:5], lcd_data[9:7]};
    assign VGA_B = {lcd_data[4:0], lcd_data[4:2]};

    // Generate sync signals from LCD mode
    // LCD modes: 0=HBlank, 1=VBlank, 2=OAM Search, 3=Pixel Transfer
    assign VGA_HS = 1'b1;  // Directly driven by lcd_clkena for simplicity
    assign VGA_VS = ~lcd_vsync;
    assign VGA_HB = (lcd_mode == 2'b00);  // HBlank
    assign VGA_VB = (lcd_mode == 2'b01);  // VBlank

    // =========================================================================
    // Audio Output (directly from GameBoy core)
    // =========================================================================
    wire [15:0] audio_l, audio_r;
    assign AUDIO_L = audio_l;
    assign AUDIO_R = audio_r;

    // =========================================================================
    // Unused signals stub
    // =========================================================================
    wire [1:0] joy_p54;
    wire [3:0] joy_din = 4'hF;  // No external controller
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
    wire [25:0] SAVE_out_Adr;
    wire        SAVE_out_rnw;
    wire        SAVE_out_ena;
    wire [7:0]  SAVE_out_be;

    assign ioctl_din = 8'h00;

    // =========================================================================
    // GameBoy Core Instantiation
    // =========================================================================
    gb gameboy (
        .reset              (reset),
        .clk_sys            (clk_sys),
        .ce                 (ce),
        .ce_n               (ce_n),
        .ce_2x              (ce_2x),

        .joystick           (joystick),
        .isGBC              (1'b0),         // DMG mode for now
        .real_cgb_boot      (1'b0),
        .isSGB              (1'b0),
        .extra_spr_en       (1'b0),

        // Cartridge interface
        .ext_bus_addr       (ext_bus_addr),
        .ext_bus_a15        (ext_bus_a15),
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
        .fast_boot_en       (1'b1),         // Enable fast boot

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
        .cart_ram_size      (8'h00),
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
        .SAVE_out_Dout      (64'h0),
        .SAVE_out_Adr       (SAVE_out_Adr),
        .SAVE_out_rnw       (SAVE_out_rnw),
        .SAVE_out_ena       (SAVE_out_ena),
        .SAVE_out_be        (SAVE_out_be),
        .SAVE_out_done      (1'b1)
    );

endmodule
