`timescale 1ps/1ps
`define ICARUS 1

// Minimal testbench to debug VSYNC alternating bug
module cga_vsync_debug_tb;

// Clocks
reg clock = 0;
reg clk_vga_cga = 0;

// Clock generation
always #10000 clock = ~clock;          // 50 MHz system clock
always #34920 clk_vga_cga = ~clk_vga_cga;  // 14.318 MHz CGA clock

// Reset
reg reset = 1;
initial begin
    #100000 reset = 0;
    #100000 reset = 1;
    #100000 reset = 0;
end

// CGA card signals
reg memaccess = 0;
reg [18:0] imem_m_addr = 0;
reg [15:0] imem_m_data_in = 0;
reg [1:0] imem_m_bytesel = 0;
reg imem_m_wr_en = 0;
wire mem_m_ack;
wire [15:0] imem_m_data_out;

// Video outputs
wire hsync, vsync;
wire [5:0] vga_r, vga_g, vga_b;
wire H_BLANK, V_BLANK, de_o_cga, std_hsyncwidth;

// Instantiate CGA card
cgacard cgacard1 (
    .clock(clock),
    .clk_vga_cga(clk_vga_cga),
    .reset(reset),

    .vga_hsync(hsync),
    .vga_vsync(vsync),
    .vga_r(vga_r),
    .vga_g(vga_g),
    .vga_b(vga_b),
    .H_BLANK(H_BLANK),
    .V_BLANK(V_BLANK),
    .de_o_cga(de_o_cga),
    .std_hsyncwidth(std_hsyncwidth),

    .regaccess(memaccess),
    .data_m_addr(imem_m_addr),
    .data_m_data_in(imem_m_data_in),
    .data_m_data_out(imem_m_data_out),
    .data_m_bytesel(imem_m_bytesel),
    .data_m_wr_en(imem_m_wr_en),
    .mem_m_ack(mem_m_ack)
);

// VSYNC edge detection
reg vsync_prev = 0;
integer vsync_count = 0;

always @(posedge clk_vga_cga) begin
    vsync_prev <= vsync;
    if (!vsync_prev && vsync) begin
        vsync_count = vsync_count + 1;
        $display("[%0t] VSYNC #%0d detected!", $time, vsync_count);
    end
end

// Task: Write CRTC register
task write_crtc_register(input [4:0] reg_addr, input [7:0] reg_data);
    begin
        // Select CRTC register
        @(posedge clock);
        memaccess = 1'b1;
        imem_m_addr = 19'h3D4 >> 1;
        imem_m_data_in = {8'h00, reg_addr};
        imem_m_bytesel = 2'b01;
        imem_m_wr_en = 1'b1;

        @(posedge clock);
        wait(mem_m_ack);

        @(posedge clock);
        memaccess = 1'b0;
        imem_m_wr_en = 1'b0;

        // Write CRTC data
        @(posedge clock);
        memaccess = 1'b1;
        imem_m_addr = 19'h3D5 >> 1;
        imem_m_data_in = {8'h00, reg_data};
        imem_m_bytesel = 2'b01;
        imem_m_wr_en = 1'b1;

        @(posedge clock);
        wait(mem_m_ack);

        @(posedge clock);
        memaccess = 1'b0;
        imem_m_wr_en = 1'b0;
        @(posedge clock);

        $display("[%0t] Wrote CRTC R%0d = 0x%02h", $time, reg_addr, reg_data);
    end
endtask

// Task: Write CGA register
task write_cga_register(input [15:0] addr, input [7:0] data);
    begin
        @(posedge clock);
        memaccess = 1'b1;
        imem_m_addr = addr >> 1;
        imem_m_data_in = {8'h00, data};
        imem_m_bytesel = 2'b01;
        imem_m_wr_en = 1'b1;

        @(posedge clock);
        wait(mem_m_ack);

        @(posedge clock);
        memaccess = 1'b0;
        imem_m_wr_en = 1'b0;
        @(posedge clock);

        $display("[%0t] Wrote CGA register 0x%04h = 0x%02h", $time, addr, data);
    end
endtask

// Task: Program Mode 03h
task program_mode_03h();
    begin
        $display("");
        $display("[%0t] ========================================", $time);
        $display("[%0t] Programming Mode 03h (80x25 text)", $time);
        $display("[%0t] ========================================", $time);

        // Disable display
        write_cga_register(16'h3D8, 8'h00);
        repeat(100) @(posedge clk_vga_cga);

        // Program CRTC
        write_crtc_register(5'h00, 8'd113);
        write_crtc_register(5'h01, 8'd80);
        write_crtc_register(5'h02, 8'd90);
        write_crtc_register(5'h03, 8'd10);
        write_crtc_register(5'h04, 8'd31);
        write_crtc_register(5'h05, 8'd0);
        write_crtc_register(5'h06, 8'd25);
        write_crtc_register(5'h09, 8'd7);
        write_crtc_register(5'h07, 8'd28);  // R7 last

        // Enable display
        write_cga_register(16'h3D8, 8'h09);

        $display("[%0t] Mode 03h programming complete", $time);
    end
endtask

// Main test
initial begin
    $display("========================================");
    $display("CGA VSYNC Debug Test");
    $display("Testing alternating VSYNC bug");
    $display("========================================");

    // Wait for reset
    wait(~reset);
    repeat(1000) @(posedge clk_vga_cga);

    // Test 1: Program Mode 03h first time
    program_mode_03h();
    $display("[%0t] Waiting for VSYNC (Test 1)...", $time);
    vsync_count = 0;
    repeat(400000) @(posedge clk_vga_cga);
    if (vsync_count > 0)
        $display("[%0t] Test 1 PASS: Got %0d VSYNCs", $time, vsync_count);
    else
        $display("[%0t] Test 1 FAIL: Got 0 VSYNCs", $time);

    // Test 2: Program Mode 03h second time (same mode)
    program_mode_03h();
    $display("[%0t] Waiting for VSYNC (Test 2)...", $time);
    vsync_count = 0;
    repeat(400000) @(posedge clk_vga_cga);
    if (vsync_count > 0)
        $display("[%0t] Test 2 PASS: Got %0d VSYNCs", $time, vsync_count);
    else
        $display("[%0t] Test 2 FAIL: Got 0 VSYNCs", $time);

    // Test 3: Program Mode 03h third time
    program_mode_03h();
    $display("[%0t] Waiting for VSYNC (Test 3)...", $time);
    vsync_count = 0;
    repeat(400000) @(posedge clk_vga_cga);
    if (vsync_count > 0)
        $display("[%0t] Test 3 PASS: Got %0d VSYNCs", $time, vsync_count);
    else
        $display("[%0t] Test 3 FAIL: Got 0 VSYNCs", $time);

    $display("");
    $display("========================================");
    $display("Debug test complete");
    $display("========================================");
    $finish;
end

// Timeout
initial begin
    #100000000;  // 100ms
    $display("TIMEOUT!");
    $finish;
end

endmodule
