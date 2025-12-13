// GameBoy RTL Unit Test - GUI Raster Sanity
//
// Validates that the GUI-facing "VGA-ish" timing produced by gameboy_sim.v
// can be consumed as a 160x144 raster when sampled at the 4MHz CE rate.
//
// This specifically catches the common GUI failure mode where the rasterizer
// is clocked at 64MHz sysclk (16x oversampling) which clamps/smears the image
// and often appears as a solid white screen.
//

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdio>
#include <cstdint>
#include <vector>

static bool load_file(const char* path, std::vector<uint8_t>& out) {
    FILE* f = fopen(path, "rb");
    if (!f) return false;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz <= 0) { fclose(f); return false; }
    out.resize((size_t)sz);
    const size_t n = fread(out.data(), 1, (size_t)sz, f);
    fclose(f);
    return n == (size_t)sz;
}

static void download_boot_rom(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* boot, size_t boot_size) {
    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < (int)boot_size; addr += 2) {
        uint16_t word = boot[addr];
        if (addr + 1 < (int)boot_size) word |= (uint16_t)boot[addr + 1] << 8;
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);
}

static void simulate_cart_download(Vtop* dut, MisterSDRAMModel* sdram, size_t rom_size) {
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;

    run_cycles_with_sdram(dut, sdram, 128);

    auto pulse_word = [&](uint32_t byte_addr) {
        if (byte_addr + 1 >= rom_size) return;
        const uint8_t lo = sdram->read8(byte_addr);
        const uint8_t hi = sdram->read8(byte_addr + 1);
        dut->ioctl_addr = byte_addr;
        dut->ioctl_dout = (uint16_t)lo | ((uint16_t)hi << 8);
        dut->ioctl_wr = 1;
        run_cycles_with_sdram(dut, sdram, 8);
        dut->ioctl_wr = 0;
        run_cycles_with_sdram(dut, sdram, 64);
    };

    const uint32_t header_end = (rom_size < 0x160) ? (uint32_t)rom_size : 0x160;
    for (uint32_t a = 0; a + 1 < header_end; a += 2) pulse_word(a);

    const uint32_t last_addr = (rom_size >= 2) ? ((uint32_t)rom_size - 2) & ~1u : 0;
    if (last_addr >= header_end) pulse_word(last_addr);

    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 1000);
}

struct FrameStats {
    uint32_t lines = 0;
    uint32_t active_samples = 0;
    uint32_t lcd_hist[4] = {0, 0, 0, 0};
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    const char* rom_path = (argc > 1) ? argv[1] : "game.gb";

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    std::vector<uint8_t> rom;
    if (!load_file(rom_path, rom)) {
        fprintf(stderr, "FAIL: cannot open ROM: %s\n", rom_path);
        return 1;
    }
    sdram->loadBinary(0, rom.data(), rom.size());

    std::vector<uint8_t> boot;
    if (!load_file("dmg_boot.bin", boot) && !load_file("../dmg_boot.bin", boot)) {
        fprintf(stderr, "FAIL: dmg_boot.bin not found\n");
        return 1;
    }
    if (boot.size() != 256) {
        fprintf(stderr, "FAIL: dmg_boot.bin size %zu != 256\n", boot.size());
        return 1;
    }

    // Reset and download boot/cart metadata.
    reset_dut_with_sdram(dut, sdram, 100);
    download_boot_rom(dut, sdram, boot.data(), boot.size());
    simulate_cart_download(dut, sdram, rom.size());

    // Release reset after a short settle.
    run_cycles_with_sdram(dut, sdram, 300);
    dut->reset = 0;

    TestResults results;
    results.set_suite("GUI Raster Sanity");

    // Sample the GUI-facing signals at the CE rate.
    // We treat each CE tick as one "dot time" (not sysclk).
    const uint32_t max_ce_frames = 8;
    const uint32_t min_expected_lines = 130;
    const uint32_t max_expected_lines = 160;
    const uint32_t min_expected_pixels = 20000;
    const uint32_t max_expected_pixels = 30000;

    uint8_t last_hs = 1;
    uint8_t last_vs = 1;
    FrameStats cur{};
    FrameStats best{};
    bool saw_any_frame = false;
    bool saw_any_nonwhite = false;
    uint32_t ce_frames = 0;

    // Run for up to ~max_ce_frames frames; upper-bound via sysclk cycles.
    // ~1.1M sysclk/frame at 64MHz; keep this fast for unit testing.
    const unsigned long max_sysclk_cycles = 25000000UL;
    for (unsigned long cyc = 0; cyc < max_sysclk_cycles && ce_frames < max_ce_frames; cyc++) {
        tick_with_sdram(dut, sdram);

        if (!dut->dbg_ce_cpu) continue;

        // Count line boundaries on falling HS outside VBlank.
        if (last_hs && !dut->VGA_HS && !dut->VGA_VB) {
            cur.lines++;
        }

        // Count active samples (DE=!(HB||VB)).
        if (!dut->VGA_HB && !dut->VGA_VB) {
            cur.active_samples++;
            const uint8_t px = dut->dbg_lcd_data_gb;
            if (px < 4) cur.lcd_hist[px]++;
            if (px != 0) saw_any_nonwhite = true;
        }

        // Frame boundary on falling VS.
        if (last_vs && !dut->VGA_VS) {
            saw_any_frame = true;
            ce_frames++;

            if (cur.active_samples > best.active_samples) best = cur;

            // Reset per-frame stats
            cur = FrameStats{};
        }

        last_hs = dut->VGA_HS;
        last_vs = dut->VGA_VS;
    }

    results.check(saw_any_frame, "Observed at least one CE frame");
    results.check(best.lines >= min_expected_lines && best.lines <= max_expected_lines, "Line count in expected range");
    results.check(best.active_samples >= min_expected_pixels && best.active_samples <= max_expected_pixels, "Active samples in expected range");
    results.check(saw_any_nonwhite, "Observed non-white pixels (GB shades != 0)");

    printf("  [INFO] best_frame: lines=%u active=%u lcd_gb=[%u,%u,%u,%u]\n",
           best.lines, best.active_samples,
           best.lcd_hist[0], best.lcd_hist[1], best.lcd_hist[2], best.lcd_hist[3]);

    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
