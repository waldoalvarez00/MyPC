// Comprehensive LCD diagnostics test
// Purpose: Determine why lcd_data_gb reads as black (3) instead of varying
//
// This test monitors:
// 1. Boot ROM execution progress
// 2. VRAM write operations
// 3. Palette register writes
// 4. LCD controller state changes
// 5. Actual lcd_data_gb values during different LCD modes

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <map>

//=============================================================================
// Boot ROM with detailed diagnostics
//=============================================================================
void createDiagnosticBootROM(uint8_t* boot_rom) {
    memset(boot_rom, 0, 256);
    int pc = 0;

    // 1. Turn off LCD
    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0xE0;  // LDH ($FF40), A
    boot_rom[pc++] = 0x40;

    // 2. Set palette to 0xE4 (standard DMG palette)
    boot_rom[pc++] = 0x3E;  // LD A, $E4
    boot_rom[pc++] = 0xE4;
    boot_rom[pc++] = 0xE0;  // LDH ($FF47), A
    boot_rom[pc++] = 0x47;

    // 3. Write simple alternating pattern to tile 0
    boot_rom[pc++] = 0x21;  // LD HL, $8000
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x80;

    // Write alternating 0xFF and 0x00 (should produce alternating colors)
    boot_rom[pc++] = 0x3E;  // LD A, $FF
    boot_rom[pc++] = 0xFF;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x22;  // LD (HL+), A

    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x22;  // LD (HL+), A

    boot_rom[pc++] = 0x3E;  // LD A, $AA  (alternating bits)
    boot_rom[pc++] = 0xAA;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x22;  // LD (HL+), A

    boot_rom[pc++] = 0x3E;  // LD A, $55  (alternating bits)
    boot_rom[pc++] = 0x55;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x22;  // LD (HL+), A

    // Fill rest of tile with 0x00
    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x06;  // LD B, $08
    boot_rom[pc++] = 0x08;
    int loop1 = pc;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x05;  // DEC B
    boot_rom[pc++] = 0x20;  // JR NZ, loop1
    boot_rom[pc++] = (uint8_t)(loop1 - (pc + 1));

    // 4. Fill tilemap with tile 0
    boot_rom[pc++] = 0x21;  // LD HL, $9800
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x98;
    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x06;  // LD B, $00
    boot_rom[pc++] = 0x00;
    int loop2 = pc;
    boot_rom[pc++] = 0x22;  // LD (HL+), A
    boot_rom[pc++] = 0x05;  // DEC B
    boot_rom[pc++] = 0x20;  // JR NZ, loop2
    boot_rom[pc++] = (uint8_t)(loop2 - (pc + 1));

    // 5. Turn on LCD
    boot_rom[pc++] = 0x3E;  // LD A, $91
    boot_rom[pc++] = 0x91;
    boot_rom[pc++] = 0xE0;  // LDH ($FF40), A
    boot_rom[pc++] = 0x40;

    // 6. Infinite loop
    int halt = pc;
    boot_rom[pc++] = 0x18;  // JR halt
    boot_rom[pc++] = (uint8_t)(halt - (pc + 1) - 1);

    printf("  Diagnostic boot ROM: %d bytes\n", pc);
}

//=============================================================================
// Download boot ROM (16-bit word writes)
//=============================================================================
void downloadBootROM(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* boot_data, size_t size) {
    dut->boot_download = 1;
    tick_with_sdram(dut, sdram);

    for (size_t addr = 0; addr < size; addr += 2) {
        uint16_t word = boot_data[addr];
        if (addr + 1 < size) {
            word |= (boot_data[addr + 1] << 8);
        }

        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }

        dut->boot_wr = 0;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
    }

    dut->boot_download = 0;

    for (int i = 0; i < 200; i++) {
        tick_with_sdram(dut, sdram);
    }
}

//=============================================================================
// Load minimal cart ROM
//=============================================================================
void loadMinimalCart(Vtop* dut, MisterSDRAMModel* sdram) {
    uint8_t cart[0x150];
    memset(cart, 0, sizeof(cart));

    // Entry point: infinite loop
    cart[0x100] = 0x18;
    cart[0x101] = 0xFE;

    // Nintendo logo
    const uint8_t logo[] = {
        0xCE,0xED,0x66,0x66,0xCC,0x0D,0x00,0x0B,0x03,0x73,0x00,0x83,0x00,0x0C,0x00,0x0D,
        0x00,0x08,0x11,0x1F,0x88,0x89,0x00,0x0E,0xDC,0xCC,0x6E,0xE6,0xDD,0xDD,0xD9,0x99,
        0xBB,0xBB,0x67,0x63,0x6E,0x0E,0xEC,0xCC,0xDD,0xDC,0x99,0x9F,0xBB,0xB9,0x33,0x3E
    };
    memcpy(&cart[0x104], logo, sizeof(logo));

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    tick_with_sdram(dut, sdram);

    for (size_t i = 0; i < sizeof(cart); i++) {
        dut->ioctl_addr = i;
        dut->ioctl_dout = cart[i];
        dut->ioctl_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->ioctl_wr = 0;
    }

    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 10);
}

//=============================================================================
// Main diagnostic test
//=============================================================================
int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== LCD Comprehensive Diagnostics ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

    // Reset
    reset_dut_with_sdram(dut, sdram, 100);

    // Create and load boot ROM
    uint8_t boot_rom[256];
    createDiagnosticBootROM(boot_rom);
    downloadBootROM(dut, sdram, boot_rom, 256);

    // Load cart ROM
    loadMinimalCart(dut, sdram);

    printf("\n=== Running Simulation ===\n");

    // Track various states
    int last_lcd_mode = -1;
    uint8_t last_ce_cpu = 0;
    int ce_cpu_count = 0;
    int frames = 0;

    // Track lcd_data_gb distribution
    std::map<int, int> lcd_gb_histogram;
    std::map<int, int> lcd_gb_by_mode[4];  // Per LCD mode

    // Sample VGA outputs during mode 3
    struct Sample {
        uint64_t cycle;
        uint8_t mode;
        uint8_t lcd_gb;
        uint8_t r, g, b;
    };
    std::vector<Sample> samples;
    samples.reserve(100);

    // Run simulation
    for (uint64_t cycle = 0; cycle < 30000000; cycle++) {
        tick_with_sdram(dut, sdram);

        // Count ce_cpu pulses
        if (dut->dbg_ce_cpu && !last_ce_cpu) {
            ce_cpu_count++;
        }
        last_ce_cpu = dut->dbg_ce_cpu;

        // Track LCD mode transitions
        if (dut->dbg_lcd_mode != last_lcd_mode) {
            if (dut->dbg_lcd_mode == 1 && last_lcd_mode == 0) {
                frames++;
                if (frames <= 3) {
                    printf("\n[Frame %d at cycle %lu]\n", frames, cycle);
                    printf("  ce_cpu pulses: %d\n", ce_cpu_count);
                    printf("  isGBC_game: %d\n", dut->dbg_isGBC_game);

                    printf("  lcd_data_gb distribution:\n");
                    for (int i = 0; i < 4; i++) {
                        printf("    Color %d: %d samples\n", i, lcd_gb_histogram[i]);
                    }

                    printf("  lcd_data_gb by mode:\n");
                    for (int m = 0; m < 4; m++) {
                        int total = 0;
                        for (int i = 0; i < 4; i++) {
                            total += lcd_gb_by_mode[m][i];
                        }
                        if (total > 0) {
                            printf("    Mode %d: ", m);
                            for (int i = 0; i < 4; i++) {
                                if (lcd_gb_by_mode[m][i] > 0) {
                                    printf("c%d=%d ", i, lcd_gb_by_mode[m][i]);
                                }
                            }
                            printf("\n");
                        }
                    }
                }
            }
            last_lcd_mode = dut->dbg_lcd_mode;
        }

        // Collect lcd_data_gb statistics
        lcd_gb_histogram[dut->dbg_lcd_data_gb]++;
        lcd_gb_by_mode[dut->dbg_lcd_mode][dut->dbg_lcd_data_gb]++;

        // Sample during mode 3 (pixel transfer)
        if (dut->dbg_lcd_mode == 3 && samples.size() < 100) {
            Sample s;
            s.cycle = cycle;
            s.mode = dut->dbg_lcd_mode;
            s.lcd_gb = dut->dbg_lcd_data_gb;
            s.r = dut->VGA_R;
            s.g = dut->VGA_G;
            s.b = dut->VGA_B;
            samples.push_back(s);
        }

        // Stop after 3 frames
        if (frames >= 3) {
            break;
        }
    }

    // Final analysis
    printf("\n=== Final Analysis ===\n");
    printf("Total ce_cpu pulses: %d\n", ce_cpu_count);
    printf("Frames rendered: %d\n", frames);
    printf("Pixel samples collected: %zu\n", samples.size());

    printf("\nOverall lcd_data_gb distribution:\n");
    for (int i = 0; i < 4; i++) {
        printf("  Color %d: %d samples\n", i, lcd_gb_histogram[i]);
    }

    if (samples.size() > 0) {
        printf("\nFirst 20 pixel samples during mode 3:\n");
        for (size_t i = 0; i < std::min((size_t)20, samples.size()); i++) {
            printf("  [%2zu] cycle=%lu mode=%d lcd_gb=%d RGB=(%3d,%3d,%3d)\n",
                   i, samples[i].cycle, samples[i].mode, samples[i].lcd_gb,
                   samples[i].r, samples[i].g, samples[i].b);
        }
    }

    printf("\n=== Diagnosis ===\n");

    if (ce_cpu_count == 0) {
        printf("❌ CPU NOT RUNNING - ce_cpu never pulsed\n");
    } else {
        printf("✅ CPU running (%d ce_cpu pulses)\n", ce_cpu_count);
    }

    if (frames == 0) {
        printf("❌ LCD NOT ACTIVE - no frames rendered\n");
    } else {
        printf("✅ LCD active (%d frames)\n", frames);
    }

    if (dut->dbg_isGBC_game) {
        printf("❌ WRONG MODE - isGBC_game=1 (should be DMG mode for game.gb)\n");
    } else {
        printf("✅ Correct mode - isGBC_game=0 (DMG)\n");
    }

    // Check if lcd_data_gb varies
    int colors_seen = 0;
    for (int i = 0; i < 4; i++) {
        if (lcd_gb_histogram[i] > 0) colors_seen++;
    }

    if (colors_seen == 1) {
        printf("❌ lcd_data_gb CONSTANT - always showing color %d\n",
               lcd_gb_histogram[0] > 0 ? 0 : lcd_gb_histogram[1] > 0 ? 1 : lcd_gb_histogram[2] > 0 ? 2 : 3);

        if (lcd_gb_histogram[3] > 0 && lcd_gb_histogram[3] == lcd_gb_histogram[0] + lcd_gb_histogram[1] + lcd_gb_histogram[2]) {
            printf("   → All pixels BLACK - possible issues:\n");
            printf("      1. VRAM not initialized (boot ROM not running)\n");
            printf("      2. Palette inverted\n");
            printf("      3. LCD reading wrong VRAM data\n");
        } else if (lcd_gb_histogram[0] > 0) {
            printf("   → All pixels WHITE - possible issues:\n");
            printf("      1. VRAM reads as 0x00\n");
            printf("      2. Palette inverted\n");
        }
    } else {
        printf("✅ lcd_data_gb varies - %d different colors seen\n", colors_seen);
        printf("   DMG conversion should be working!\n");
    }

    // Check VGA outputs
    bool all_black = true;
    for (const auto& s : samples) {
        if (s.r != 0 || s.g != 0 || s.b != 0) {
            all_black = false;
            break;
        }
    }

    if (all_black && samples.size() > 0) {
        printf("❌ VGA OUTPUTS ALL BLACK despite lcd_data_gb values\n");
        printf("   → Check DMG conversion logic in gameboy_sim.v\n");
    } else if (!all_black) {
        printf("✅ VGA outputs varying - display should work!\n");
    }

    delete sdram;
    delete dut;

    return 0;
}
