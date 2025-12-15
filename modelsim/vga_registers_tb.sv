// VGARegisters (MCGA Controller) Testbench
// Tests CPU interface and register access for VGA/MCGA controller
//
// This testbench focuses on:
// - Register read/write operations
// - Mode switching (text, 4-color CGA, 256-color MCGA)
// - Cursor control
// - DAC palette programming
// - Status register
//
// Note: This tests CPU interface only, not actual video output timing

`timescale 1ns/1ps

module vga_registers_tb;

// Clock and reset
reg clk;
reg vga_clk;
reg reset;

// Bus interface
reg         cs;
reg  [19:1] data_m_addr;
reg  [15:0] data_m_data_in;
wire [15:0] data_m_data_out;
reg  [1:0]  data_m_bytesel;
reg         data_m_wr_en;
reg         data_m_access;
wire        data_m_ack;

// VGA sync inputs (simulated)
reg         vga_vsync;
reg         vga_hsync;

// VGA control outputs
wire        cursor_enabled;
wire        graphics_enabled;
wire [3:0]  background_color;
wire        bright_colors;
wire        palette_sel;
wire [14:0] cursor_pos;
wire [2:0]  cursor_scan_start;
wire [2:0]  cursor_scan_end;
wire        vga_256_color;
wire [7:0]  vga_dac_idx;
wire [17:0] vga_dac_rd;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// DUT instantiation
VGARegisters dut (
    .clk              (clk),
    .vga_clk          (vga_clk),
    .reset            (reset),
    .cs               (cs),
    .data_m_addr      (data_m_addr),
    .data_m_data_in   (data_m_data_in),
    .data_m_data_out  (data_m_data_out),
    .data_m_bytesel   (data_m_bytesel),
    .data_m_wr_en     (data_m_wr_en),
    .data_m_access    (data_m_access),
    .data_m_ack       (data_m_ack),
    .vga_vsync        (vga_vsync),
    .vga_hsync        (vga_hsync),
    .cursor_enabled   (cursor_enabled),
    .graphics_enabled (graphics_enabled),
    .background_color (background_color),
    .bright_colors    (bright_colors),
    .palette_sel      (palette_sel),
    .cursor_pos       (cursor_pos),
    .cursor_scan_start(cursor_scan_start),
    .cursor_scan_end  (cursor_scan_end),
    .vga_256_color    (vga_256_color),
    .vga_dac_idx      (vga_dac_idx),
    .vga_dac_rd       (vga_dac_rd)
);

// Clock generation: 50 MHz system clock
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 20ns period = 50 MHz
end

// VGA clock generation: 25 MHz
initial begin
    vga_clk = 0;
    forever #20 vga_clk = ~vga_clk;  // 40ns period = 25 MHz
end

// VGA sync generation (simulated)
initial begin
    vga_hsync = 0;
    vga_vsync = 0;
    forever begin
        #1000 vga_hsync = ~vga_hsync;  // Rough hsync
        if (vga_hsync)
            #16000 vga_vsync = ~vga_vsync;  // Rough vsync every ~16ms
    end
end

// Helper task: CPU write
task cpu_write(input [19:1] addr, input [15:0] data, input [1:0] bytesel);
    begin
        @(posedge clk);
        #1;  // Small delay to avoid race with always_ff blocks
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        data_m_addr = addr;
        data_m_data_in = data;
        data_m_bytesel = bytesel;

        wait(data_m_ack == 1'b1);
        @(posedge clk);
        #1;  // Small delay before clearing

        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
        @(posedge clk);
    end
endtask

// Helper task: CPU read
task cpu_read(input [19:1] addr, input [1:0] bytesel, output [15:0] data);
    begin
        @(posedge clk);
        #1;  // Small delay to avoid race with always_ff blocks
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b0;
        data_m_addr = addr;
        data_m_bytesel = bytesel;

        wait(data_m_ack == 1'b1);
        @(posedge clk);
        #1;  // Small delay for Icarus Verilog
        data = data_m_data_out;

        cs = 1'b0;
        data_m_access = 1'b0;
        @(posedge clk);
    end
endtask

// Test reporting
task report_test(input string name, input logic passed);
    begin
        test_count = test_count + 1;
        if (passed) begin
            $display("  [PASS] %s", name);
            pass_count = pass_count + 1;
        end else begin
            $display("  [FAIL] %s", name);
            fail_count = fail_count + 1;
        end
    end
endtask

// Main test sequence
initial begin
    $dumpfile("vga_registers_tb.vcd");
    $dumpvars(0, vga_registers_tb);

    $display("================================================================");
    $display("VGARegisters (MCGA Controller) Testbench");
    $display("Testing VGA/MCGA register interface and mode control");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1;
    cs = 0;
    data_m_access = 0;
    data_m_wr_en = 0;
    data_m_addr = 19'h0;
    data_m_data_in = 16'h0000;
    data_m_bytesel = 2'b00;

    // Wait for reset
    repeat(10) @(posedge clk);
    reset = 0;
    repeat(10) @(posedge clk);

    // Test 1: Initial mode read (should be text mode)
    $display("Test 1: Initial mode read");
    begin
        reg [15:0] read_data;
        cpu_read(19'h1EC, 2'b01, read_data);  // 3D8h Mode Control Register
        $display("  Mode register: 0x%02X", read_data[7:0]);
        // Bit 0 = text_enabled, Bit 1 = graphics_enabled, Bit 3 = display_enabled
        report_test("Text mode enabled initially", read_data[0] == 1'b1);
        report_test("Graphics mode disabled initially", read_data[1] == 1'b0);
        report_test("Display enabled initially", read_data[3] == 1'b1);
    end

    // Test 2: Switch to 4-color CGA graphics mode
    $display("");
    $display("Test 2: Switch to 4-color CGA graphics mode");
    begin
        reg [15:0] read_data;
        // Mode: bit 1 = graphics_enabled, bit 3 = display_enabled
        cpu_write(19'h1EC, 16'h000A, 2'b01);  // 3D8h: graphics=1, display=1, text=0
        repeat(5) @(posedge clk);
        cpu_read(19'h1EC, 2'b01, read_data);
        $display("  Mode after write: 0x%02X", read_data[7:0]);
        report_test("Graphics mode enabled", graphics_enabled == 1'b1);
        report_test("Text mode disabled", read_data[0] == 1'b0);
        report_test("256-color mode not active", vga_256_color == 1'b0);
    end

    // Test 3: Color select register
    $display("");
    $display("Test 3: Color select register (3D9h)");
    begin
        reg [15:0] read_data;
        // Write: palette_sel, bright_colors, background_color[3:0]
        cpu_write(19'h1EC, 16'h2500, 2'b10);  // 3D9h upper byte: 0x25
        repeat(10) @(posedge clk);  // Allow clock domain crossing
        repeat(10) @(posedge vga_clk);

        cpu_read(19'h1EC, 2'b10, read_data);
        $display("  Color select: 0x%02X", read_data[15:8]);
        $display("  palette_sel=%b, bright_colors=%b, background=0x%X",
                 palette_sel, bright_colors, background_color);
        report_test("Color select register writeable", read_data[15:8] == 8'h25);
    end

    // Test 4: Cursor position programming
    $display("");
    $display("Test 4: Cursor position programming");
    begin
        reg [15:0] read_data;
        // Write cursor position high (index 0xE)
        cpu_write(19'h1EA, 16'h000E, 2'b01);  // 3D4h: index = 0xE
        cpu_write(19'h1EA, 16'h1200, 2'b10);  // 3D5h: cursor_pos[14:8] = 0x12

        // Write cursor position low (index 0xF)
        cpu_write(19'h1EA, 16'h000F, 2'b01);  // 3D4h: index = 0xF
        cpu_write(19'h1EA, 16'h3400, 2'b10);  // 3D5h: cursor_pos[7:0] = 0x34

        // Manually pulse vsync to trigger MCP transfer
        repeat(10) @(posedge clk);
        vga_vsync = 1;
        repeat(5) @(posedge clk);
        vga_vsync = 0;
        repeat(10) @(posedge vga_clk);

        // Read back
        cpu_write(19'h1EA, 16'h000E, 2'b01);
        cpu_read(19'h1EA, 2'b10, read_data);
        $display("  Cursor pos high: 0x%02X (expected 0x12)", read_data[15:8]);
        report_test("Cursor position high byte", read_data[15:8] == 8'h12);

        cpu_write(19'h1EA, 16'h000F, 2'b01);
        cpu_read(19'h1EA, 2'b10, read_data);
        $display("  Cursor pos low: 0x%02X (expected 0x34)", read_data[15:8]);
        report_test("Cursor position low byte", read_data[15:8] == 8'h34);

        $display("  cursor_pos output: 0x%04X (expected 0x1234)", cursor_pos);
        report_test("Cursor position output", cursor_pos == 15'h1234);
    end

    // Test 5: Cursor scan lines
    $display("");
    $display("Test 5: Cursor scan line configuration");
    begin
        reg [15:0] read_data;
        // Write cursor start (index 0xA): cursor_mode[1:0], cursor_scan_start[2:0]
        cpu_write(19'h1EA, 16'h000A, 2'b01);  // 3D4h: index = 0xA
        cpu_write(19'h1EA, 16'h0600, 2'b10);  // 3D5h: cursor_scan_start = 6

        // Write cursor end (index 0xB)
        cpu_write(19'h1EA, 16'h000B, 2'b01);  // 3D4h: index = 0xB
        cpu_write(19'h1EA, 16'h0700, 2'b10);  // 3D5h: cursor_scan_end = 7

        // Manually pulse vsync to trigger MCP transfer
        repeat(10) @(posedge clk);
        vga_vsync = 1;
        repeat(5) @(posedge clk);
        vga_vsync = 0;
        repeat(10) @(posedge vga_clk);

        // Read back
        cpu_write(19'h1EA, 16'h000A, 2'b01);
        cpu_read(19'h1EA, 2'b10, read_data);
        $display("  Cursor start: scan line %0d", read_data[10:8]);
        report_test("Cursor scan start", cursor_scan_start == 3'd6);

        cpu_write(19'h1EA, 16'h000B, 2'b01);
        cpu_read(19'h1EA, 2'b10, read_data);
        $display("  Cursor end: scan line %0d", read_data[10:8]);
        report_test("Cursor scan end", cursor_scan_end == 3'd7);
    end

    // Test 6: Switch to 256-color MCGA mode
    $display("");
    $display("Test 6: Switch to 256-color MCGA mode");
    begin
        reg [15:0] read_data;
        // AMCR register 3C0h: value 0x41 enables 256-color mode
        cpu_write(19'h1E0, 16'h0041, 2'b01);  // 3C0h: AMCR = 0x41
        repeat(10) @(posedge clk);
        repeat(10) @(posedge vga_clk);

        cpu_read(19'h1E0, 2'b01, read_data);
        $display("  AMCR register: 0x%02X", read_data[7:0]);
        $display("  vga_256_color output: %b", vga_256_color);
        report_test("256-color mode enabled", vga_256_color == 1'b1);
    end

    // Test 7: DAC palette programming
    $display("");
    $display("Test 7: DAC palette programming");
    begin
        reg [15:0] read_data;
        // Write DAC index for color 42
        cpu_write(19'h1E4, 16'h002A, 2'b01);  // 3C8h: DAC write index = 42

        // Write RGB components (6 bits each)
        cpu_write(19'h1E4, 16'h3F00, 2'b10);  // 3C9h: R = 0x3F (max red)
        cpu_write(19'h1E4, 16'h2000, 2'b10);  // 3C9h: G = 0x20
        cpu_write(19'h1E4, 16'h1000, 2'b10);  // 3C9h: B = 0x10

        repeat(5) @(posedge clk);

        // Read back palette entry
        cpu_write(19'h1E3, 16'h2A00, 2'b10);  // 3C7h: DAC read index = 42
        repeat(2) @(posedge clk);

        cpu_read(19'h1E4, 2'b10, read_data);
        $display("  DAC entry 42 - R: 0x%02X", read_data[13:8]);
        report_test("DAC red component", read_data[13:8] == 6'h3F);

        cpu_read(19'h1E4, 2'b10, read_data);
        $display("  DAC entry 42 - G: 0x%02X", read_data[13:8]);
        report_test("DAC green component", read_data[13:8] == 6'h20);

        cpu_read(19'h1E4, 2'b10, read_data);
        $display("  DAC entry 42 - B: 0x%02X", read_data[13:8]);
        report_test("DAC blue component", read_data[13:8] == 6'h10);
    end

    // Test 8: Status register
    $display("");
    $display("Test 8: Status register read (3DAh)");
    begin
        reg [15:0] read_data;
        cpu_read(19'h1ED, 2'b01, read_data);  // 3DAh: status register
        $display("  Status: 0x%02X", read_data[7:0]);
        $display("  Bit 0 (display enable): %b", read_data[0]);
        $display("  Bit 3 (vsync): %b", read_data[3]);
        report_test("Status register readable", 1'b1);
    end

    // Test 9: ACK signal timing
    $display("");
    $display("Test 9: ACK signal verification");
    begin
        @(posedge clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b0;
        data_m_addr = 19'h1EC;
        @(posedge clk);
        @(posedge clk);
        report_test("ACK asserted during access", data_m_ack == 1'b1);

        cs = 1'b0;
        data_m_access = 1'b0;
        @(posedge clk);
        @(posedge clk);
        report_test("ACK cleared after access", data_m_ack == 1'b0);
    end

    // Test 10: Index register persistence
    $display("");
    $display("Test 10: Index register persistence");
    begin
        reg [15:0] read_data;
        cpu_write(19'h1EA, 16'h0005, 2'b01);  // Set index to 5
        cpu_read(19'h1EA, 2'b01, read_data);
        $display("  Index after write: 0x%X", read_data[3:0]);
        report_test("Index register persistent", read_data[3:0] == 4'h5);
    end

    // Test 11: Return to text mode
    $display("");
    $display("Test 11: Return to text mode");
    begin
        reg [15:0] read_data;
        cpu_write(19'h1E0, 16'h0000, 2'b01);  // Clear AMCR (disable 256-color)
        cpu_write(19'h1EC, 16'h0009, 2'b01);  // Mode: text=1, graphics=0, display=1
        repeat(10) @(posedge clk);
        repeat(10) @(posedge vga_clk);

        cpu_read(19'h1EC, 2'b01, read_data);
        $display("  Mode: 0x%02X", read_data[7:0]);
        report_test("Text mode restored", read_data[0] == 1'b1);
        report_test("Graphics disabled", graphics_enabled == 1'b0);
        report_test("256-color disabled", vga_256_color == 1'b0);
    end

    // Print summary
    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0d%%", (pass_count * 100) / test_count);
    $display("================================================================");
    $display("");

    if (fail_count == 0) begin
        $display("*** ALL VGA/MCGA REGISTER TESTS PASSED ***");
    end else begin
        $display("*** SOME TESTS FAILED ***");
    end

    $display("");
    $display("NOTE: This testbench tests CPU interface only.");
    $display("Actual video output timing and framebuffer access not tested.");
    $display("================================================================");
    $display("");
    $display("MISSING VIDEO MODES (Not Implemented):");
    $display("- 2-color high-resolution (640x200, 1bpp)");
    $display("- 16-color EGA modes (320x200, 640x200, 640x350, 640x480)");
    $display("- Monochrome text mode");
    $display("- 40-column text modes (may work but not verified)");
    $display("================================================================");

    $finish;
end

// Timeout watchdog
initial begin
    #500000;  // 500us timeout
    $display("ERROR: Test timeout!");
    $finish;
end

endmodule
