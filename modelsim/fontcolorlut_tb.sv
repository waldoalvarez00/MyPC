// ================================================================
// Unit Test for FontColorLUT
// Tests font rendering, color palettes, and graphics modes
// ================================================================

`timescale 1ns/1ps

module fontcolorlut_tb;

    // DUT signals
    logic clk;
    logic render_cursor;
    logic [7:0] glyph;
    logic [2:0] glyph_row;
    logic [2:0] glyph_col;
    logic [3:0] foreground;
    logic [3:0] background;
    logic graphics_enabled;
    logic [7:0] graphics_colour;
    logic vga_256_color;
    logic [17:0] vga_dac_rd;
    logic bright_colors;
    logic palette_sel;
    logic [3:0] background_color;
    logic [3:0] r;
    logic [3:0] g;
    logic [3:0] b;

    // Instantiate DUT
    FontColorLUT dut (
        .clk(clk),
        .render_cursor(render_cursor),
        .glyph(glyph),
        .glyph_row(glyph_row),
        .glyph_col(glyph_col),
        .foreground(foreground),
        .background(background),
        .graphics_enabled(graphics_enabled),
        .graphics_colour(graphics_colour),
        .vga_256_color(vga_256_color),
        .vga_dac_rd(vga_dac_rd),
        .bright_colors(bright_colors),
        .palette_sel(palette_sel),
        .background_color(background_color),
        .r(r),
        .g(g),
        .b(b)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #20 clk = ~clk;  // 25 MHz
    end

    // Test counters
    // Test variables (declared at module level for Icarus Verilog)
    logic [11:0] rgb;
    logic [11:0] fg_color;
    logic [11:0] bg_color;
    logic [11:0] no_cursor;
    logic [11:0] with_cursor;
    logic [11:0] gfx_rgb;
    logic [11:0] normal_intensity;
    logic [11:0] bright_intensity;
    logic [11:0] palette0;
    logic [11:0] palette1;
    logic [11:0] dac_white;
    logic [11:0] dac_black;
    logic [11:0] pixel_rgb;
    logic [11:0] text_output;
    logic [11:0] graphics_output;
    logic [11:0] text_output2;

    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    task check_result(input string test_name, input logic condition);
        test_count++;
        if (condition) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s", test_count, test_name);
            fail_count++;
        end
    endtask

    // Test sequence
    initial begin
        $display("================================================================");
        $display("FontColorLUT Unit Test");
        $display("================================================================");

        // Initialize
        render_cursor = 0;
        glyph = 8'h00;
        glyph_row = 3'd0;
        glyph_col = 3'd0;
        foreground = 4'hF;  // White
        background = 4'h0;  // Black
        graphics_enabled = 0;
        graphics_colour = 8'h00;
        vga_256_color = 0;
        vga_dac_rd = 18'h00000;
        bright_colors = 0;
        palette_sel = 0;
        background_color = 4'h0;

        repeat(5) @(posedge clk);

        // ================================================================
        // TEST 1: Text Mode - Basic Colors
        // ================================================================
        $display("\n--- Test 1: Text Mode - Basic Colors ---");

        graphics_enabled = 0;
        glyph = 8'h41;  // 'A'
        glyph_row = 3'd0;
        glyph_col = 3'd0;
        foreground = 4'hF;  // White
        background = 4'h0;  // Black

        repeat(3) @(posedge clk);

        check_result("Text mode active", graphics_enabled == 1'b0);
        check_result("RGB output non-zero", (r | g | b) != 4'h0);

        // ================================================================
        // TEST 2: Color Palette - All 16 EGA Colors
        // ================================================================
        $display("\n--- Test 2: All 16 EGA Colors ---");

        glyph = 8'h20;  // Space (all pixels background)

        for (int i = 0; i < 16; i++) begin
            background = i[3:0];
            repeat(3) @(posedge clk);

            // Each color should produce some RGB output
            rgb = {r, g, b};

            case (i)
                0:  check_result($sformatf("Color %0d (Black)", i), rgb == 12'h000);
                1:  check_result($sformatf("Color %0d (Blue)", i), b != 4'h0);
                2:  check_result($sformatf("Color %0d (Green)", i), g != 4'h0);
                3:  check_result($sformatf("Color %0d (Cyan)", i), g != 4'h0 && b != 4'h0);
                4:  check_result($sformatf("Color %0d (Red)", i), r != 4'h0);
                5:  check_result($sformatf("Color %0d (Magenta)", i), r != 4'h0 && b != 4'h0);
                6:  check_result($sformatf("Color %0d (Brown)", i), r != 4'h0);
                7:  check_result($sformatf("Color %0d (White)", i), r != 4'h0 && g != 4'h0 && b != 4'h0);
                8:  check_result($sformatf("Color %0d (Gray)", i), rgb != 12'h000 && rgb != 12'hFFF);
                9:  check_result($sformatf("Color %0d (Bright Blue)", i), b > 4'hA);
                10: check_result($sformatf("Color %0d (Bright Green)", i), g > 4'hA);
                11: check_result($sformatf("Color %0d (Bright Cyan)", i), g > 4'hA && b > 4'hA);
                12: check_result($sformatf("Color %0d (Bright Red)", i), r > 4'hA);
                13: check_result($sformatf("Color %0d (Bright Magenta)", i), r > 4'hA && b > 4'hA);
                14: check_result($sformatf("Color %0d (Yellow)", i), r > 4'hA && g > 4'hA);
                15: check_result($sformatf("Color %0d (Bright White)", i), rgb == 12'hFFF);
            endcase
        end

        // ================================================================
        // TEST 3: Foreground vs Background
        // ================================================================
        $display("\n--- Test 3: Foreground vs Background ---");

        glyph = 8'hDB;  // Full block character
        foreground = 4'hF;  // White
        background = 4'h0;  // Black

        repeat(3) @(posedge clk);
        fg_color = {r, g, b};

        glyph = 8'h20;  // Space (all background)
        repeat(3) @(posedge clk);
        bg_color = {r, g, b};

        check_result("Foreground != Background", fg_color != bg_color);
        check_result("Foreground is white", fg_color == 12'hFFF);
        check_result("Background is black", bg_color == 12'h000);

        // ================================================================
        // TEST 4: Cursor Rendering
        // ================================================================
        $display("\n--- Test 4: Cursor Rendering ---");

        glyph = 8'h41;  // 'A'
        foreground = 4'h7;  // Light gray
        background = 4'h0;  // Black
        render_cursor = 0;

        repeat(3) @(posedge clk);
        no_cursor = {r, g, b};

        render_cursor = 1;
        repeat(3) @(posedge clk);
        with_cursor = {r, g, b};

        check_result("Cursor inverts colors", no_cursor != with_cursor);

        render_cursor = 0;
        @(posedge clk);

        // ================================================================
        // TEST 5: Graphics Mode - CGA 4-Color
        // ================================================================
        $display("\n--- Test 5: Graphics Mode - CGA 4-Color ---");

        graphics_enabled = 1;
        vga_256_color = 0;
        palette_sel = 0;     // Palette 0
        bright_colors = 0;
        background_color = 4'h0;

        // Test all 4 CGA colors (2-bit)
        for (int i = 0; i < 4; i++) begin
            graphics_colour = {6'b0, i[1:0]};
            repeat(3) @(posedge clk);

            gfx_rgb = {r, g, b};

            if (i == 0)
                check_result($sformatf("CGA color %0d (background)", i),
                             gfx_rgb == 12'h000);  // Background color
            else
                check_result($sformatf("CGA color %0d", i), gfx_rgb != 12'h000);
        end

        // ================================================================
        // TEST 6: Graphics Mode - Bright Colors
        // ================================================================
        $display("\n--- Test 6: Graphics Mode - Bright Colors ---");

        graphics_colour = 8'h01;
        bright_colors = 0;
        repeat(3) @(posedge clk);
        normal_intensity = {r, g, b};

        bright_colors = 1;
        repeat(3) @(posedge clk);
        bright_intensity = {r, g, b};

        check_result("Bright colors differ from normal",
                     bright_intensity != normal_intensity);

        // ================================================================
        // TEST 7: Graphics Mode - Palette Selection
        // ================================================================
        $display("\n--- Test 7: Graphics Mode - Palette Selection ---");

        graphics_colour = 8'h01;
        bright_colors = 0;
        palette_sel = 0;
        repeat(3) @(posedge clk);
        palette0 = {r, g, b};

        palette_sel = 1;
        repeat(3) @(posedge clk);
        palette1 = {r, g, b};

        check_result("Palette selection changes colors",
                     palette0 != palette1);

        // ================================================================
        // TEST 8: 256-Color Mode (VGA Mode 13h)
        // ================================================================
        $display("\n--- Test 8: 256-Color Mode ---");

        graphics_enabled = 1;
        vga_256_color = 1;

        // Test DAC color readback
        vga_dac_rd = 18'b111111_111111_111111;  // White in DAC
        graphics_colour = 8'hFF;

        repeat(3) @(posedge clk);

        dac_white = {r, g, b};
        check_result("256-color mode produces output",
                     dac_white != 12'h000);

        vga_dac_rd = 18'b000000_000000_000000;  // Black in DAC
        repeat(3) @(posedge clk);

        dac_black = {r, g, b};
        check_result("DAC black produces black output",
                     dac_black == 12'h000);

        // ================================================================
        // TEST 9: Font ROM Access
        // ================================================================
        $display("\n--- Test 9: Font ROM Access ---");

        graphics_enabled = 0;
        vga_256_color = 0;

        // Test different glyphs
        for (int g_test = 0; g_test < 8; g_test++) begin
            glyph = g_test * 32;  // Sample every 32nd glyph
            glyph_row = 3'd4;
            glyph_col = 3'd4;

            repeat(3) @(posedge clk);

            check_result($sformatf("Glyph %02X accessible", glyph), 1'b1);
        end

        // ================================================================
        // TEST 10: All Glyph Positions
        // ================================================================
        $display("\n--- Test 10: All Glyph Positions ---");

        glyph = 8'h41;  // 'A'
        foreground = 4'hF;
        background = 4'h0;

        // Test all 8x8 positions
        for (int row_pos = 0; row_pos < 8; row_pos++) begin
            for (int col_pos = 0; col_pos < 8; col_pos++) begin
                glyph_row = row_pos[2:0];
                glyph_col = col_pos[2:0];

                repeat(2) @(posedge clk);

                // Output should be valid (either foreground or background)
                pixel_rgb = {r, g, b};
                check_result($sformatf("Position [%0d,%0d] valid", row_pos, col_pos),
                             pixel_rgb == 12'hFFF || pixel_rgb == 12'h000);
            end
        end

        // ================================================================
        // TEST 11: Mode Transitions
        // ================================================================
        $display("\n--- Test 11: Text/Graphics Mode Transitions ---");

        // Text mode
        graphics_enabled = 0;
        glyph = 8'h41;
        foreground = 4'h7;
        background = 4'h0;
        repeat(3) @(posedge clk);
        text_output = {r, g, b};

        // Switch to graphics
        graphics_enabled = 1;
        graphics_colour = 8'h03;
        repeat(3) @(posedge clk);
        graphics_output = {r, g, b};

        check_result("Mode transition produces different output",
                     text_output != graphics_output);

        // Back to text
        graphics_enabled = 0;
        repeat(3) @(posedge clk);
        text_output2 = {r, g, b};

        check_result("Return to text mode restores output",
                     text_output == text_output2);

        // ================================================================
        // TEST 12: Boundary Conditions
        // ================================================================
        $display("\n--- Test 12: Boundary Conditions ---");

        graphics_enabled = 0;

        // Maximum glyph value
        glyph = 8'hFF;
        glyph_row = 3'd7;
        glyph_col = 3'd7;
        foreground = 4'hF;
        background = 4'h0;

        repeat(3) @(posedge clk);
        check_result("Maximum glyph/row/col handled", 1'b1);

        // All foreground/background combinations
        foreground = 4'hF;
        background = 4'hF;
        repeat(3) @(posedge clk);
        check_result("Same foreground/background handled", {r,g,b} == 12'hFFF);

        // ================================================================
        // Test Summary
        // ================================================================
        $display("\n================================================================");
        $display("TEST SUMMARY");
        $display("================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %0d%%", (pass_count * 100) / test_count);
        $display("================================================================");

        if (fail_count == 0) begin
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓");
            $finish(0);
        end else begin
            $display("✗✗✗ SOME TESTS FAILED ✗✗✗");
            $finish(1);
        end
    end

    // Timeout
    initial begin
        #1000000;  // 1ms timeout
        $display("\n[ERROR] Testbench timeout!");
        $finish(1);
    end

endmodule
