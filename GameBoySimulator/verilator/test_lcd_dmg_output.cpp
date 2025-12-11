// GameBoy RTL Unit Test - LCD DMG Output
// Tests the complete video pipeline from VRAM writes to pixel output
//
// This test creates a minimal boot ROM that:
// 1. Initializes the LCD
// 2. Writes a test pattern to VRAM (black/white stripes)
// 3. Enables LCD output
// 4. Verifies VGA_R/VGA_G/VGA_B signals show expected grayscale values

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

//=============================================================================
// Boot ROM Helper - Create minimal LCD test pattern boot ROM
//=============================================================================
void createLCDTestBootROM(uint8_t* boot_rom) {
    memset(boot_rom, 0, 256);
    int pc = 0;

    // 1. Turn off LCD (required before VRAM access)
    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0xE0;  // LDH ($FF40), A ; LCDC off
    boot_rom[pc++] = 0x40;

    // 2. Set palette to 0xE4 (11 10 01 00 binary)
    // Bit pairs: 3=Black, 2=Dark Gray, 1=Light Gray, 0=White
    boot_rom[pc++] = 0x3E;  // LD A, $E4
    boot_rom[pc++] = 0xE4;
    boot_rom[pc++] = 0xE0;  // LDH ($FF47), A ; BGP palette
    boot_rom[pc++] = 0x47;

    // 3. Write tile pattern at $8000 (Tile 0)
    // Top half: 0xFF (all bits 1 = color 3 = black with palette 0xE4)
    // Bottom half: 0x00 (all bits 0 = color 0 = white with palette 0xE4)
    boot_rom[pc++] = 0x21;  // LD HL, $8000
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x80;

    // Write 8 bytes of 0xFF (top 4 rows)
    boot_rom[pc++] = 0x3E;  // LD A, $FF
    boot_rom[pc++] = 0xFF;
    boot_rom[pc++] = 0x06;  // LD B, $08
    boot_rom[pc++] = 0x08;
    int loop1 = pc;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x05;  // DEC B
    boot_rom[pc++] = 0x20;  // JR NZ, loop1
    boot_rom[pc++] = (uint8_t)(loop1 - (pc + 1));

    // Write 8 bytes of 0x00 (bottom 4 rows)
    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x06;  // LD B, $08
    boot_rom[pc++] = 0x08;
    int loop2 = pc;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x05;  // DEC B
    boot_rom[pc++] = 0x20;  // JR NZ, loop2
    boot_rom[pc++] = (uint8_t)(loop2 - (pc + 1));

    // 4. Fill tilemap with tile 0
    boot_rom[pc++] = 0x21;  // LD HL, $9800
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x98;
    boot_rom[pc++] = 0x3E;  // LD A, $00  ; Tile index 0
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x06;  // LD B, $00  ; 256 iterations
    boot_rom[pc++] = 0x00;
    int loop3 = pc;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x05;  // DEC B
    boot_rom[pc++] = 0x20;  // JR NZ, loop3
    boot_rom[pc++] = (uint8_t)(loop3 - (pc + 1));

    // 5. Turn on LCD with BG enabled
    boot_rom[pc++] = 0x3E;  // LD A, $91
    boot_rom[pc++] = 0x91;  // LCD on, BG on, window off, sprites off
    boot_rom[pc++] = 0xE0;  // LDH ($FF40), A
    boot_rom[pc++] = 0x40;

    // 6. Infinite loop (stay in boot ROM for testing)
    int halt_loop = pc;
    boot_rom[pc++] = 0x18;  // JR halt_loop
    boot_rom[pc++] = (uint8_t)(halt_loop - (pc + 1) - 1);

    printf("  LCD test boot ROM: %d bytes\n", pc);
    printf("  Pattern: Tile with black/white horizontal stripes\n");
}

//=============================================================================
// Download boot ROM
//=============================================================================
void downloadBootROM(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* boot_data, size_t size) {
    printf("  Downloading boot ROM (%zu bytes)...\n", size);

    dut->boot_download = 1;
    tick_with_sdram(dut, sdram);

    // Write 16-bit words (2 bytes at a time) like GUI simulator does
    for (size_t addr = 0; addr < size; addr += 2) {
        uint16_t word = boot_data[addr];
        if (addr + 1 < size) {
            word |= (boot_data[addr + 1] << 8);
        }

        dut->boot_addr = addr;  // Byte address
        dut->boot_data = word;
        dut->boot_wr = 1;

        // Run 8 cycles with write active
        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }

        dut->boot_wr = 0;

        // Run 8 more cycles after write
        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
    }

    dut->boot_download = 0;

    // Run cycles to stabilize
    for (int i = 0; i < 200; i++) {
        tick_with_sdram(dut, sdram);
    }

    printf("  Boot ROM download complete\n");
}

//=============================================================================
// Load minimal cart ROM
//=============================================================================
void loadMinimalCartROM(Vtop* dut, MisterSDRAMModel* sdram) {
    printf("  Loading minimal cart ROM...\n");

    // Prepare minimal cart ROM bytes
    uint8_t cart_rom[0x150];
    memset(cart_rom, 0, sizeof(cart_rom));

    // Entry point at 0x100: infinite loop
    cart_rom[0x100] = 0x18;  // JR $100
    cart_rom[0x101] = 0xFE;

    // Nintendo logo (required for boot validation)
    const uint8_t logo[] = {
        0xCE,0xED,0x66,0x66,0xCC,0x0D,0x00,0x0B,0x03,0x73,0x00,0x83,0x00,0x0C,0x00,0x0D,
        0x00,0x08,0x11,0x1F,0x88,0x89,0x00,0x0E,0xDC,0xCC,0x6E,0xE6,0xDD,0xDD,0xD9,0x99,
        0xBB,0xBB,0x67,0x63,0x6E,0x0E,0xEC,0xCC,0xDD,0xDC,0x99,0x9F,0xBB,0xB9,0x33,0x3E
    };
    memcpy(&cart_rom[0x104], logo, sizeof(logo));

    // Use ioctl interface to load ROM
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;  // ROM index
    tick_with_sdram(dut, sdram);

    for (size_t i = 0; i < sizeof(cart_rom); i++) {
        dut->ioctl_addr = i;
        dut->ioctl_dout = cart_rom[i];
        dut->ioctl_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->ioctl_wr = 0;
    }

    dut->ioctl_download = 0;
    tick_with_sdram(dut, sdram);

    // Wait for cart_ready
    run_cycles_with_sdram(dut, sdram, 10);

    printf("  Cart ROM loaded, cart_ready=%d\n", dut->dbg_cart_ready);
}

//=============================================================================
// Test: LCD DMG pixel output
//=============================================================================
void test_lcd_dmg_pixel_output(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("LCD DMG Pixel Output");

    // Reset
    reset_dut_with_sdram(dut, sdram, 100);

    // Create and download LCD test boot ROM
    uint8_t boot_rom[256];
    createLCDTestBootROM(boot_rom);
    downloadBootROM(dut, sdram, boot_rom, 256);

    // Load cart ROM
    loadMinimalCartROM(dut, sdram);

    // Release reset and let boot ROM run
    printf("  Running simulation...\n");

    // Warmup: Let clock divider stabilize
    run_cycles_with_sdram(dut, sdram, 1000);

    // Track LCD state
    int lcd_mode_changes = 0;
    int last_lcd_mode = -1;
    int frames_seen = 0;
    bool lcd_became_active = false;

    // Track ce_cpu edges
    int ce_cpu_edges = 0;
    uint8_t last_ce_cpu = 0;

    // Track CPU address to see if boot ROM is executing
    uint16_t sample_cpu_addrs[10];
    int addr_samples = 0;

    // Collect pixel samples during active display
    struct PixelSample {
        uint8_t r, g, b;
    };
    std::vector<PixelSample> samples;
    samples.reserve(1000);

    // Run for up to 30M cycles (enough to see boot ROM execute)
    for (uint64_t cycle = 0; cycle < 30000000; cycle++) {
        tick_with_sdram(dut, sdram);

        // Track ce_cpu edges
        if (dut->dbg_ce_cpu && !last_ce_cpu) {
            ce_cpu_edges++;
        }
        last_ce_cpu = dut->dbg_ce_cpu;

        // Track LCD mode transitions
        if (dut->dbg_lcd_mode != last_lcd_mode) {
            lcd_mode_changes++;

            // Frame complete when entering VBlank (mode 1) from HBlank (mode 0)
            if (dut->dbg_lcd_mode == 1 && last_lcd_mode == 0) {
                frames_seen++;
                if (frames_seen <= 3) {
                    printf("  Frame %d complete at cycle %lu\n", frames_seen, cycle);
                }
            }

            if (!lcd_became_active && dut->dbg_lcd_mode != 0) {
                lcd_became_active = true;
                printf("  LCD became active at cycle %lu (mode %d)\n", cycle, dut->dbg_lcd_mode);
            }

            last_lcd_mode = dut->dbg_lcd_mode;
        }

        // Sample pixels during pixel transfer (mode 3) after LCD becomes active
        if (dut->dbg_lcd_mode == 3 && lcd_became_active && samples.size() < 1000) {
            PixelSample s;
            s.r = dut->VGA_R;
            s.g = dut->VGA_G;
            s.b = dut->VGA_B;
            samples.push_back(s);
        }

        // Sample CPU address periodically
        if (cycle % 1000000 == 0 && addr_samples < 10) {
            sample_cpu_addrs[addr_samples++] = dut->dbg_cpu_addr;
        }

        // Progress reports every 10M cycles
        if (cycle > 0 && cycle % 10000000 == 0) {
            printf("  [%lu M] ce_cpu_edges=%d, lcd_mode=%d, VGA RGB=(%d,%d,%d)\n",
                   cycle / 1000000, ce_cpu_edges, dut->dbg_lcd_mode,
                   dut->VGA_R, dut->VGA_G, dut->VGA_B);
            ce_cpu_edges = 0;  // Reset counter for next window
        }

        // Stop after 3 complete frames
        if (frames_seen >= 3) {
            printf("  Stopping after %d frames (%lu cycles)\n", frames_seen, cycle);
            break;
        }
    }

    // Analyze results
    printf("\n  Analysis:\n");
    printf("    LCD mode changes: %d\n", lcd_mode_changes);
    printf("    Frames seen: %d\n", frames_seen);
    printf("    Pixel samples: %zu\n", samples.size());

    // Check critical debug signals
    printf("\n  Debug signals at end:\n");
    printf("    isGBC_game: %d (0=DMG, 1=GBC)\n", dut->dbg_isGBC_game);
    printf("    lcd_data: 0x%04X (15-bit RGB555)\n", dut->dbg_lcd_data);
    printf("    lcd_data_gb: %d (2-bit DMG color)\n", dut->dbg_lcd_data_gb);
    printf("    VGA_R: %d, VGA_G: %d, VGA_B: %d\n", dut->VGA_R, dut->VGA_G, dut->VGA_B);

    printf("\n  CPU address samples:\n");
    for (int i = 0; i < addr_samples; i++) {
        printf("    [%d] 0x%04X\n", i, sample_cpu_addrs[i]);
    }

    results.check(lcd_became_active, "LCD became active");
    results.check(lcd_mode_changes > 10, "LCD mode transitions detected");
    results.check(frames_seen >= 1, "At least 1 frame rendered");

    if (samples.size() > 0) {
        // Count color distribution
        int black_count = 0, white_count = 0, gray_count = 0;

        for (const auto& s : samples) {
            if (s.r == 0 && s.g == 0 && s.b == 0) {
                black_count++;
            } else if (s.r == 255 && s.g == 255 && s.b == 255) {
                white_count++;
            } else {
                gray_count++;
            }
        }

        printf("\n  Pixel color distribution:\n");
        printf("    Black (0,0,0):       %d (%.1f%%)\n", black_count, 100.0 * black_count / samples.size());
        printf("    White (255,255,255): %d (%.1f%%)\n", white_count, 100.0 * white_count / samples.size());
        printf("    Gray (other):        %d (%.1f%%)\n", gray_count, 100.0 * gray_count / samples.size());

        // Print first 20 samples
        printf("\n  First 20 pixel samples:\n");
        for (size_t i = 0; i < std::min((size_t)20, samples.size()); i++) {
            printf("    [%2zu] RGB=(%3d, %3d, %3d)\n", i, samples[i].r, samples[i].g, samples[i].b);
        }

        // Verification
        results.check(samples.size() >= 100, "Sufficient pixel samples collected");

        if (black_count == samples.size()) {
            results.check(false, "All pixels BLACK - DMG monochrome conversion NOT working");
        } else if (white_count > 0) {
            results.check(true, "WHITE pixels detected - DMG conversion working!");
        } else {
            results.check(gray_count > 0, "Non-black pixels detected");
        }

    } else {
        results.check(false, "No pixel samples collected");
    }
}

//=============================================================================
// Main
//=============================================================================
int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    TestResults results;

    printf("=== GameBoy LCD DMG Output Test ===\n");

    test_lcd_dmg_pixel_output(dut, sdram, results);

    delete sdram;
    delete dut;

    return results.report();
}
