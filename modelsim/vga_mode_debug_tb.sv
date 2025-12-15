// VGA Mode Detection Debug Testbench
// Simple test to debug mode detection issues

`timescale 1ns/1ps

`include "VGATypes.sv"

module vga_mode_debug_tb;

// Clocks
logic sys_clk;
logic vga_clk;
logic reset;

// VGARegisters interface
logic cs;
logic [19:1] data_m_addr;
logic [15:0] data_m_data_in;
logic [15:0] data_m_data_out;
logic [1:0] data_m_bytesel;
logic data_m_wr_en;
logic data_m_access;
logic data_m_ack;

// Outputs
logic cursor_enabled;
logic graphics_enabled;
logic [3:0] background_color;
logic bright_colors;
logic palette_sel;
logic [14:0] cursor_pos;
logic [2:0] cursor_scan_start;
logic [2:0] cursor_scan_end;
logic vga_256_color;
logic [7:0] vga_dac_idx;
logic [17:0] vga_dac_rd;
VideoModeNumber_t mode_num;

// Clock generation
initial begin
    sys_clk = 0;
    forever #10 sys_clk = ~sys_clk;  // 50 MHz
end

initial begin
    vga_clk = 0;
    forever #20 vga_clk = ~vga_clk;  // 25 MHz
end

// DUT: VGARegisters
VGARegisters VGARegisters(
    .clk(sys_clk),
    .vga_clk(vga_clk),
    .reset(reset),
    .cs(cs),
    .data_m_addr(data_m_addr),
    .data_m_data_in(data_m_data_in),
    .data_m_data_out(data_m_data_out),
    .data_m_bytesel(data_m_bytesel),
    .data_m_wr_en(data_m_wr_en),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .vga_vsync(1'b0),
    .vga_hsync(1'b0),
    .cursor_enabled(cursor_enabled),
    .graphics_enabled(graphics_enabled),
    .background_color(background_color),
    .bright_colors(bright_colors),
    .palette_sel(palette_sel),
    .cursor_pos(cursor_pos),
    .cursor_scan_start(cursor_scan_start),
    .cursor_scan_end(cursor_scan_end),
    .vga_256_color(vga_256_color),
    .vga_dac_idx(vga_dac_idx),
    .vga_dac_rd(vga_dac_rd),
    .mode_num(mode_num)
);

// Monitor internal signals
always @(posedge sys_clk) begin
    if (cs && data_m_wr_en && data_m_ack) begin
        $display("[%0t] Write to addr=0x%h (%0d decimal) = 0b%b",
                 $time, data_m_addr, data_m_addr, data_m_addr);
        $display("    data=%h, bytesel=%b", data_m_data_in, data_m_bytesel);
        $display("    addr[4:1]=%b (%0d decimal)", data_m_addr[4:1], data_m_addr[4:1]);
        $display("    Expected for MODE: 4'b0110 (6 decimal)");
        $display("    reg_access=%b, sel_mode=%b, sel_amcr=%b",
                 VGARegisters.reg_access, VGARegisters.sel_mode, VGARegisters.sel_amcr);
    end
end

always @(VGARegisters.sys_graphics_enabled or VGARegisters.text_enabled or VGARegisters.sys_256_color) begin
    $display("[%0t] Internal: graphics_en=%b, text_en=%b, 256color=%b, mode_num=%h",
             $time, VGARegisters.sys_graphics_enabled,
             VGARegisters.text_enabled,
             VGARegisters.sys_256_color,
             VGARegisters.sys_mode_num);
end

// Register write task
task write_register(input [19:1] addr, input [15:0] data, input [1:0] bytesel);
    begin
        $display("[%0t] Starting write: addr=%h, data=%h, bytesel=%b",
                 $time, addr, data, bytesel);

        @(posedge sys_clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = addr;
        data_m_data_in = data;
        data_m_bytesel = bytesel;

        @(posedge sys_clk);
        while (!data_m_ack) @(posedge sys_clk);

        @(posedge sys_clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;

        $display("[%0t] Write complete", $time);
    end
endtask

// Main test
initial begin
    $display("================================================================");
    $display("VGA Mode Detection Debug Test");
    $display("================================================================");

    // Initialize
    reset = 1'b1;
    cs = 1'b0;
    data_m_access = 1'b0;
    data_m_wr_en = 1'b0;
    data_m_addr = 19'h0;
    data_m_data_in = 16'h0;
    data_m_bytesel = 2'b00;

    repeat(10) @(posedge sys_clk);
    reset = 1'b0;
    repeat(10) @(posedge sys_clk);

    $display("");
    $display("After reset:");
    $display("  mode_num = %h (expected 03h)", mode_num);
    repeat(10) @(posedge vga_clk);
    $display("  mode_num = %h (after vga_clk sync)", mode_num);

    $display("");
    $display("Writing 0x0A to 3D8h (addr=1ECh) to enable graphics mode...");
    write_register(19'h1EC, 16'h000A, 2'b01);

    $display("");
    $display("After write to 3D8h:");
    $display("  Internal sys_graphics_enabled = %b", VGARegisters.sys_graphics_enabled);
    $display("  Internal text_enabled = %b", VGARegisters.text_enabled);
    $display("  Internal sys_mode_num = %h", VGARegisters.sys_mode_num);

    repeat(10) @(posedge vga_clk);
    $display("");
    $display("After VGA clock sync:");
    $display("  mode_num = %h (expected 04h)", mode_num);

    #1000;
    $finish;
end

// Timeout
initial begin
    #50000;
    $display("ERROR: Test timeout!");
    $finish;
end

endmodule
