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
#include <algorithm>

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

static void init_cart_without_writes(Vtop* dut, MisterSDRAMModel* sdram) {
    // Match the "minimal cart init" flow used by the CPU unit tests:
    //  - Pulse ioctl_download high (no writes) so cart regs reset deterministically.
    //  - Pulse ioctl_wr once with ioctl_download low to generate dn_write and set cart_ready.
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);

    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);
}

struct FrameStats {
    uint32_t lines = 0;
    uint32_t active_samples = 0;
    uint32_t nonwhite_samples = 0;
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

    // Hold the core in reset while we inject the boot ROM and initialize cart state.
    // If reset is released too early, the CPU can start executing with an empty boot ROM
    // and before cart_ready is asserted, leading to permanent 0x00 reads from ROM.
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    download_boot_rom(dut, sdram, boot.data(), boot.size());
    init_cart_without_writes(dut, sdram);
    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 5000, sdram);

    // Release reset after a short settle.
    run_cycles_with_sdram(dut, sdram, 500);
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
    bool saw_any_nonwhite_after_boot = false;
    uint32_t ce_frames = 0;

    // Additional boot/video instrumentation
    bool saw_boot_disable = false;
    unsigned long sysclk_at_boot_disable = 0;
    uint32_t vram_writes = 0;
    uint32_t vram_reads = 0;
    uint32_t vram_reads_nonzero = 0;
    uint32_t bg_fetch_reload = 0;
    uint32_t cpu_wr_n_low_cycles = 0;
    uint32_t video_cpu_wr_pulses = 0;
    uint8_t min_cpu_wr_n = 1, max_cpu_wr_n = 0;
    uint8_t min_old_cpu_wr_n = 1, max_old_cpu_wr_n = 0;
    uint8_t min_cpu_wr_n_edge = 1, max_cpu_wr_n_edge = 0;
    uint32_t tile_shift_nonzero_cycles = 0;
    uint32_t bg_pix_nonzero_cycles = 0;
    uint8_t min_bg_pix = 3, max_bg_pix = 0;
    uint32_t bg_pix_hist[4] = {0, 0, 0, 0};
    uint32_t tilemap_reads = 0;
    uint32_t tilemap_reads_nonzero = 0;
    uint32_t tiledata_reads = 0;
    uint32_t tiledata_reads_nonzero = 0;

    uint8_t prev_cpu_wr_n = 1;
    uint32_t cpu_wr_falls = 0;
    uint32_t cpu_wr_falls_vram = 0;
    uint32_t cpu_wr_falls_io = 0;
    uint32_t cpu_wr_falls_hram = 0;
    uint32_t cpu_wr_falls_other = 0;

    uint32_t vram_write_falls = 0;
    uint32_t vram_write_falls_nonzero = 0;
    uint32_t vram_write_tiledata = 0;
    uint32_t vram_write_tiledata_nonzero = 0;
    uint32_t vram_write_tilemap = 0;
    uint32_t vram_write_tilemap_nonzero = 0;
    uint32_t vram_write_falls_allowed = 0;
    uint32_t vram_write_falls_blocked = 0;
    uint32_t vram_cpu_allow_high = 0;
    uint32_t vram_cpu_allow_low = 0;
    uint32_t vram_cpu_allow_high_after_lcd_on = 0;
    uint32_t vram_cpu_allow_low_after_lcd_on = 0;
    uint32_t boot_sel_cycles = 0;
    uint32_t boot_sel_ce_cycles = 0;
    uint32_t cart_header_reads = 0;
    uint8_t header_0104_0107[4] = {0, 0, 0, 0};
    bool header_0104_0107_seen[4] = {false, false, false, false};
    bool header_0104_0107_any_nonzero = false;
    uint8_t header_0104_0107_last[4] = {0, 0, 0, 0};
    uint16_t header_sdram_do_last[4] = {0, 0, 0, 0};
    uint32_t header_sdram_addr_last[4] = {0, 0, 0, 0};
    uint32_t header_mbc_addr_last[4] = {0, 0, 0, 0};
    uint8_t header_sel_boot_rom_last[4] = {0, 0, 0, 0};
    uint8_t header_cart_ready_last[4] = {0, 0, 0, 0};
    uint8_t header_cart_rd_last[4] = {0, 0, 0, 0};
    uint8_t header_sel_ext_bus_last[4] = {0, 0, 0, 0};
    uint8_t header_cpu_iorq_n_last[4] = {1, 1, 1, 1};
    uint8_t bgp_first = 0;
    uint8_t bgp_last = 0;
    uint8_t lcdc_first = 0;
    uint8_t lcdc_last = 0;
    bool captured_regs = false;

    // Only start scoring frames after the boot ROM disables (FF50=1).
    // This avoids false "non-white" observations during power-on/transients.
    bool scoring_enabled = false;
    const uint32_t max_scored_frames = 6;
    uint32_t scored_frames = 0;

    // Run for up to ~max_ce_frames frames; upper-bound via sysclk cycles.
    // ~1.1M sysclk/frame at 64MHz; keep this fast for unit testing.
    const unsigned long max_sysclk_cycles = 25000000UL;
    for (unsigned long cyc = 0; cyc < max_sysclk_cycles && ce_frames < max_ce_frames; cyc++) {
        // Manual tick so we can sample short-lived pulses on the rising edge.
        dut->clk_sys = 1;
        dut->eval();

        // Process SDRAM on rising edge (same as gb_test_common.h).
        uint16_t rdata = dut->sd_data_in;
        bool compl_out = false;
        bool config_done = false;
        sdram->processNativeSDRAM(
            dut->sd_cs,
            dut->sd_ras,
            dut->sd_cas,
            dut->sd_we,
            dut->sd_ba,
            dut->sd_addr,
            dut->sd_data_out,
            dut->sd_dqm,
            rdata,
            compl_out,
            config_done
        );
        dut->sd_data_in = rdata;

        // ---- Rising-edge sample point ----

        // Capture/track a few regs once the core is out of reset and running.
        if (!captured_regs && !dut->reset) {
            bgp_first = dut->dbg_video_bgp;
            lcdc_first = dut->dbg_lcdc;
            captured_regs = true;
        }
        bgp_last = dut->dbg_video_bgp;
        lcdc_last = dut->dbg_lcdc;

        // Track boot ROM disable; start "real" scoring from that point.
        if (!saw_boot_disable && dut->dbg_boot_rom_enabled == 0) {
            saw_boot_disable = true;
            sysclk_at_boot_disable = cyc;
            scoring_enabled = true;
        }

        if (dut->dbg_sel_boot_rom) {
            boot_sel_cycles++;
            if (dut->dbg_ce_cpu) boot_sel_ce_cycles++;
        }

        // Observe a few header reads as seen by the CPU bus.
        // Require an actual memory read cycle (MREQ_n=0, RD_n=0).
        if (dut->dbg_cpu_mreq_n == 0 && dut->dbg_cpu_rd_n == 0) {
            const uint16_t a = dut->dbg_cpu_addr;
            if (a >= 0x0104 && a <= 0x0107) {
                const int idx = (int)(a - 0x0104);
                header_0104_0107_last[idx] = dut->dbg_cpu_di;
                header_sdram_do_last[idx] = dut->dbg_sdram_do;
                header_sdram_addr_last[idx] = dut->dbg_sdram_addr;
                header_mbc_addr_last[idx] = dut->dbg_mbc_addr;
                header_sel_boot_rom_last[idx] = dut->dbg_sel_boot_rom;
                header_sel_ext_bus_last[idx] = dut->dbg_sel_ext_bus;
                header_cpu_iorq_n_last[idx] = dut->dbg_cpu_iorq_n;
                header_cart_ready_last[idx] = dut->dbg_cart_ready;
                header_cart_rd_last[idx] = dut->dbg_cart_rd;
                if (dut->dbg_cpu_di) header_0104_0107_any_nonzero = true;
                if (!header_0104_0107_seen[idx]) {
                    header_0104_0107_seen[idx] = true;
                    header_0104_0107[idx] = dut->dbg_cpu_di;
                }
                cart_header_reads++;
            }
        }

        if (dut->dbg_vram_wren) vram_writes++;
        if (dut->dbg_video_vram_rd) {
            vram_reads++;
            if (dut->dbg_video_vram_data) vram_reads_nonzero++;
        }
        if (dut->dbg_video_bg_reload_shift) bg_fetch_reload++;

        if (dut->dbg_cpu_wr_n == 0) cpu_wr_n_low_cycles++;
        if (dut->dbg_video_cpu_wr) video_cpu_wr_pulses++;
        min_cpu_wr_n = std::min<uint8_t>(min_cpu_wr_n, dut->dbg_cpu_wr_n);
        max_cpu_wr_n = std::max<uint8_t>(max_cpu_wr_n, dut->dbg_cpu_wr_n);
        min_old_cpu_wr_n = std::min<uint8_t>(min_old_cpu_wr_n, dut->dbg_old_cpu_wr_n);
        max_old_cpu_wr_n = std::max<uint8_t>(max_old_cpu_wr_n, dut->dbg_old_cpu_wr_n);
        min_cpu_wr_n_edge = std::min<uint8_t>(min_cpu_wr_n_edge, dut->dbg_cpu_wr_n_edge);
        max_cpu_wr_n_edge = std::max<uint8_t>(max_cpu_wr_n_edge, dut->dbg_cpu_wr_n_edge);

        if (dut->dbg_video_tile_shift_0 || dut->dbg_video_tile_shift_1) tile_shift_nonzero_cycles++;
        if (dut->dbg_video_bg_pix_data) bg_pix_nonzero_cycles++;
        min_bg_pix = std::min<uint8_t>(min_bg_pix, dut->dbg_video_bg_pix_data);
        max_bg_pix = std::max<uint8_t>(max_bg_pix, dut->dbg_video_bg_pix_data);

        // Detect write cycles using dbg_cpu_wr_n directly (more reliable than dbg_cpu_wr_n_edge,
        // which may only be a delta-cycle pulse in Verilator).
        if (prev_cpu_wr_n == 1 && dut->dbg_cpu_wr_n == 0) {
            cpu_wr_falls++;
            const uint16_t a = dut->dbg_cpu_addr;
            if ((a & 0xE000) == 0x8000) cpu_wr_falls_vram++;
            else if ((a & 0xFF00) == 0xFF00) {
                if ((a & 0xFF80) == 0xFF80 && a != 0xFFFF) cpu_wr_falls_hram++;
                else cpu_wr_falls_io++;
            } else {
                cpu_wr_falls_other++;
            }

            if ((a & 0xE000) == 0x8000) {
                vram_write_falls++;
                const uint8_t d = dut->dbg_cpu_do;
                if (d) vram_write_falls_nonzero++;
                if (dut->dbg_vram_cpu_allow) vram_write_falls_allowed++;
                else vram_write_falls_blocked++;
                if (a < 0x9800) {
                    vram_write_tiledata++;
                    if (d) vram_write_tiledata_nonzero++;
                } else {
                    vram_write_tilemap++;
                    if (d) vram_write_tilemap_nonzero++;
                }
            }
        }
        prev_cpu_wr_n = dut->dbg_cpu_wr_n;

        if (dut->dbg_vram_cpu_allow) vram_cpu_allow_high++; else vram_cpu_allow_low++;
        if (dut->dbg_lcd_on) {
            if (dut->dbg_vram_cpu_allow) vram_cpu_allow_high_after_lcd_on++;
            else vram_cpu_allow_low_after_lcd_on++;
        }

        // Only sample raster signals at the CE rate (what the GUI does).
        if (!dut->dbg_ce_cpu) {
            dut->clk_sys = 0;
            dut->eval();
            continue;
        }

        // Track BG fetch/read behavior on CE ticks (video stage updates on ce).
        if (scoring_enabled && dut->dbg_video_vram_rd) {
            const uint16_t a = dut->dbg_video_vram_addr;
            const uint8_t d = dut->dbg_video_vram_data;
            if (a >= 0x1800 && a < 0x2000) {
                tilemap_reads++;
                if (d) tilemap_reads_nonzero++;
            } else if (a < 0x1800) {
                tiledata_reads++;
                if (d) tiledata_reads_nonzero++;
            }
        }

        // Count line boundaries on falling HS outside VBlank.
        if (last_hs && !dut->VGA_HS && !dut->VGA_VB) {
            cur.lines++;
        }

        // Count active samples (DE=!(HB||VB)).
        if (!dut->VGA_HB && !dut->VGA_VB) {
            cur.active_samples++;
            const uint8_t px = dut->dbg_lcd_data_gb;
            if (px < 4) cur.lcd_hist[px]++;
            if (px != 0) cur.nonwhite_samples++;
            if (scoring_enabled && px != 0) saw_any_nonwhite_after_boot = true;

            if (scoring_enabled) {
                const uint8_t bgpx = dut->dbg_video_bg_pix_data & 3;
                bg_pix_hist[bgpx]++;
            }
        }

        // Frame boundary on falling VS.
        if (last_vs && !dut->VGA_VS) {
            saw_any_frame = true;
            ce_frames++;

            if (scoring_enabled) {
                scored_frames++;
                if (cur.active_samples > best.active_samples) best = cur;
                if (scored_frames >= max_scored_frames) break;
            }

            // Reset per-frame stats
            cur = FrameStats{};
        }

        last_hs = dut->VGA_HS;
        last_vs = dut->VGA_VS;

        // Falling edge
        dut->clk_sys = 0;
        dut->eval();
    }

    results.check(saw_any_frame, "Observed at least one CE frame");
    results.check(saw_boot_disable, "Boot ROM disabled (FF50 written)");
    results.check(best.lines >= min_expected_lines && best.lines <= max_expected_lines, "Line count in expected range");
    results.check(best.active_samples >= min_expected_pixels && best.active_samples <= max_expected_pixels, "Active samples in expected range");
    results.check(saw_any_nonwhite_after_boot, "Observed non-white pixels after boot (GB shades != 0)");

    printf("  [INFO] boot_disable=%d sysclk_at_boot_disable=%lu\n",
           saw_boot_disable ? 1 : 0, sysclk_at_boot_disable);
    printf("  [INFO] regs: lcdc(first,last)=0x%02X,0x%02X bgp(first,last)=0x%02X,0x%02X\n",
           lcdc_first, lcdc_last, bgp_first, bgp_last);
    printf("  [INFO] vram: writes=%u reads=%u reads_nonzero=%u bg_reload=%u\n",
           vram_writes, vram_reads, vram_reads_nonzero, bg_fetch_reload);
    printf("  [INFO] cpu_wr_n_low_cycles=%u video_cpu_wr_pulses=%u\n",
           cpu_wr_n_low_cycles, video_cpu_wr_pulses);
    printf("  [INFO] wr_n ranges: cpu_wr_n[min,max]=%u,%u old_cpu_wr_n[min,max]=%u,%u cpu_wr_n_edge[min,max]=%u,%u\n",
           min_cpu_wr_n, max_cpu_wr_n, min_old_cpu_wr_n, max_old_cpu_wr_n, min_cpu_wr_n_edge,
           max_cpu_wr_n_edge);
    printf("  [INFO] bg: tile_shift_nonzero_cycles=%u bg_pix_nonzero_cycles=%u bg_pix[min,max]=%u,%u\n",
           tile_shift_nonzero_cycles, bg_pix_nonzero_cycles, min_bg_pix, max_bg_pix);
    printf("  [INFO] cpu_wr_falls=%u vram=%u io=%u hram=%u other=%u\n",
           cpu_wr_falls, cpu_wr_falls_vram, cpu_wr_falls_io, cpu_wr_falls_hram, cpu_wr_falls_other);
    printf("  [INFO] vram_writes_by_cpu: total=%u nonzero=%u tiledata=%u nonzero=%u tilemap=%u nonzero=%u\n",
           vram_write_falls, vram_write_falls_nonzero, vram_write_tiledata, vram_write_tiledata_nonzero,
           vram_write_tilemap, vram_write_tilemap_nonzero);
    printf("  [INFO] vram_allow: high=%u low=%u | after_lcd_on high=%u low=%u | writes allowed=%u blocked=%u\n",
           vram_cpu_allow_high, vram_cpu_allow_low,
           vram_cpu_allow_high_after_lcd_on, vram_cpu_allow_low_after_lcd_on,
           vram_write_falls_allowed, vram_write_falls_blocked);
    printf("  [INFO] boot_sel: cycles=%u ce_cycles=%u boot_enabled_now=%u\n",
           boot_sel_cycles, boot_sel_ce_cycles, (uint32_t)dut->dbg_boot_rom_enabled);
    printf("  [INFO] cart_header_reads=%u cpu_di@0104..0107=%02X %02X %02X %02X\n",
           cart_header_reads,
           header_0104_0107[0], header_0104_0107[1], header_0104_0107[2], header_0104_0107[3]);
    printf("  [INFO] cart_header_any_nonzero=%d cpu_di_last@0104..0107=%02X %02X %02X %02X\n",
           header_0104_0107_any_nonzero ? 1 : 0,
           header_0104_0107_last[0], header_0104_0107_last[1], header_0104_0107_last[2],
           header_0104_0107_last[3]);
    printf("  [INFO] header_sdram_addr_last@0104..0107=%06X %06X %06X %06X sdram_do_last=%04X %04X %04X %04X\n",
           header_sdram_addr_last[0], header_sdram_addr_last[1], header_sdram_addr_last[2],
           header_sdram_addr_last[3], header_sdram_do_last[0], header_sdram_do_last[1],
           header_sdram_do_last[2], header_sdram_do_last[3]);
    printf("  [INFO] header_mbc_addr_last@0104..0107=%06X %06X %06X %06X\n",
           header_mbc_addr_last[0], header_mbc_addr_last[1], header_mbc_addr_last[2],
           header_mbc_addr_last[3]);
    printf("  [INFO] header_ctrl_last@0104..0107 sel_boot=%u %u %u %u sel_ext=%u %u %u %u iorq_n=%u %u %u %u cart_ready=%u %u %u %u cart_rd=%u %u %u %u\n",
           header_sel_boot_rom_last[0], header_sel_boot_rom_last[1], header_sel_boot_rom_last[2],
           header_sel_boot_rom_last[3], header_sel_ext_bus_last[0], header_sel_ext_bus_last[1],
           header_sel_ext_bus_last[2], header_sel_ext_bus_last[3], header_cpu_iorq_n_last[0],
           header_cpu_iorq_n_last[1], header_cpu_iorq_n_last[2], header_cpu_iorq_n_last[3],
           header_cart_ready_last[0], header_cart_ready_last[1], header_cart_ready_last[2],
           header_cart_ready_last[3], header_cart_rd_last[0], header_cart_rd_last[1],
           header_cart_rd_last[2], header_cart_rd_last[3]);
    printf("  [INFO] tilemap_reads=%u nonzero=%u tiledata_reads=%u nonzero=%u\n",
           tilemap_reads, tilemap_reads_nonzero, tiledata_reads, tiledata_reads_nonzero);
    printf("  [INFO] bg_pix_hist(post-boot,active)=[%u,%u,%u,%u]\n",
           bg_pix_hist[0], bg_pix_hist[1], bg_pix_hist[2], bg_pix_hist[3]);
    printf("  [INFO] best_frame(post-boot): lines=%u active=%u nonwhite=%u lcd_gb=[%u,%u,%u,%u]\n",
           best.lines, best.active_samples,
           best.nonwhite_samples,
           best.lcd_hist[0], best.lcd_hist[1], best.lcd_hist[2], best.lcd_hist[3]);

    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
