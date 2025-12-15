// Copyright 2025, Waldo Alvarez, https://pipflow.com
`default_nettype none
module cgacard(

                  input clock,
						input clk_vga_cga,
						input reset,

                   // VGA signals
		             output logic vga_hsync,
		             output logic vga_vsync,
		             output logic [5:0] vga_r,
		             output logic [5:0] vga_g,
		             output logic [5:0] vga_b,
						 
						 
						 output logic H_BLANK,
						 output logic V_BLANK,
						 
						 output wire  de_o_cga,
						 
						 output wire std_hsyncwidth,
						 
						 
						 
						 //output logic ce_pix,
						 
						 // IO Bus
						 input  wire  regaccess,
                   input  logic [19:1] data_m_addr,
                   input  logic [15:0] data_m_data_in,
                   output logic [15:0] data_m_data_out,
                   input  logic [1:0]  data_m_bytesel,
                   input  logic data_m_wr_en,
						 
                   output logic data_m_ack,
						 
						 
						 // Mem Bus
						 input  wire  memaccess,
                   input  logic [19:1] imem_m_addr,
                   input  logic [15:0] imem_m_data_in,
                   output logic [15:0] imem_m_data_out,
                   input  logic [1:0]  imem_m_bytesel,
                   input  logic imem_m_wr_en,
						 
                   output logic mem_m_ack
						 
						 
						 );
						 


	 wire [4:0] clkdiv;
    wire[3:0] video_cga;
	 wire [7:0] CGA_VRAM_DOUT;
						 
	 // CGA digital to analog converter
    cga_vgaport vga_cga 
    (
        .clk(clk_vga_cga),
        .clkdiv(clkdiv),
        .video(video_cga),
        .hblank(H_BLANK),
        .composite(1'b0 /*tandy_video ? swap_video ? ~composite : composite : composite*/),
        .red(vga_r),
        .green(vga_g),
        .blue(vga_b)
    );
	 
	 assign data_m_ack = regack;
	 
	 wire regack;
	 
	 wire CGA_VRAM_ENABLE;
	 wire [18:0] CGA_VRAM_ADDR;
	 wire grph_mode;
	 
	 wire [7:0] CGA_CRTC_DOUT;

    cga cga1
    (
        .clk                        (clk_vga_cga),
        .reset                      (reset),          // ADDED: Pass reset signal
        .clkdiv                     (clkdiv),
        .bus_a                      (data_m_addr),
        .bus_ior_l                  (~(regaccess & ~data_m_wr_en)),
        .bus_iow_l                  (~(regaccess &  data_m_wr_en)),


		  .ack_signal                 (regack),
		  
        .bus_d                      (data_m_data_in[7:0]),
        .bus_out                    (CGA_CRTC_DOUT),
        .bus_dir                    (),
        //.bus_aen                    (cga_address_enable_n_2),
        .ram_we_l                   (CGA_VRAM_ENABLE),
        .ram_a                      (CGA_VRAM_ADDR),
        .ram_d                      (CGA_VRAM_DOUT),
        .hsync                      (vga_hsync),              // non scandoubled
    //  .dbl_hsync                  (HSYNC_CGA),              // scandoubled
        .hblank                     (H_BLANK),
        .vsync                      (vga_vsync),
        .vblank                     (V_BLANK),
        .vblank_border              (),
        .std_hsyncwidth             (std_hsyncwidth),
        .de_o                       (de_o_cga),
        .video                      (video_cga),              // non scandoubled
    //  .dbl_video                  (video_cga),              // scandoubled
        //.splashscreen               (splashscreen),
        .thin_font                  (1'b0),
        //.tandy_video                (tandy_video),
        .grph_mode                  (grph_mode),
        .hres_mode                  (hres_mode),
        .tandy_color_16             (),
        .cga_hw                     (1'b1)
    );
						 
						 
    defparam cga1.BLINK_MAX = 24'd4772727;
    //defparam hgc1.BLINK_MAX = 24'd9100000;
	 
    wire [15:0] cga_vram_cpu_dout;
	 wire [15:0] vram_data_out;
	 wire hres_mode;
	 
	 wire [16:0]mem_addr;
	 wire [7:0]mem_data_in;
	 wire [7:0]mem_data_out;
	 
	 wire mem_we;
	 wire mem_en;
	 
	 busConverter #(.AW(14)) Converter
	 (
	 .outstate(),                    // Output state (not used)
	 .clk(clock),                    // Clock input
    .rst(reset),                    // Asynchronous reset, active high
	 .en(memaccess),                 // Enable signal for the module
    .we(imem_m_wr_en & memaccess),  // Write enable signal
    .data_in(imem_m_data_in),       // 16-bit data input for writing to memory
    .data_out(vram_data_out),       // 16-bit data output from reading memory
    .addr(imem_m_addr[14:1]),       // Address input for memory operations
    .bytesel(imem_m_bytesel),       // 2-bit Byte select signal
	 .bus_ack(mem_m_ack),            // Acknowledgment signal for operation completion

    .mem_addr(mem_addr),            // Output address for memory
    .mem_data_in(mem_data_in),      // 8-bit data input from memory (for reads)
    .mem_data_out(mem_data_out),    // 8-bit data output to memory (for writes)
	 .mem_we(mem_we),
	 .mem_en(mem_en)
	 );
	 

    vram #(.AW(14)) cga_vram // 14 bits = 16kb
    (
        .clka                       (clock),
        .ena                        (mem_en),
        .wea                        (mem_we),
        .addra                      (mem_addr),
        .dina                       (mem_data_out),
        .douta                      (mem_data_in),
		  
        .clkb                       (clk_vga_cga),
        .web                        (1'b0),
        .enb                        (CGA_VRAM_ENABLE),
        .addrb                      (CGA_VRAM_ADDR[13:0]),
        .dinb                       (8'h0),
        .doutb                      (CGA_VRAM_DOUT)
		  
		  
    );

assign imem_m_data_out = memaccess? vram_data_out : 16'h0000;
assign data_m_data_out = regaccess? {8'h00, CGA_CRTC_DOUT} : 16'h0000;

/*	 
always @(*) begin
    if (memaccess) begin
        // Assuming you want to output CGA_VRAM_DOUT during memory accesses
        // Note: You may need to adjust this based on how CGA_VRAM_DOUT is defined, e.g., if it needs to be expanded to 16 bits
        data_m_data_out = vram_data_out; // Zero-extend or sign-extend based on your requirements
    end else if (regaccess) begin
        // Output CGA_CRTC_DOUT during register accesses
        // Again, adjust based on the actual bit-width of CGA_CRTC_DOUT and your system's requirements
        data_m_data_out = {8'h00, CGA_CRTC_DOUT};
    end else begin
        // Default case or handle as appropriate for your system
        data_m_data_out = 16'h0000;
    end
end

*/
						 
						 
endmodule