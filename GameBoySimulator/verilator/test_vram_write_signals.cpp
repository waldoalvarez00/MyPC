// Test to monitor VRAM write signals
// Purpose: Check if cpu_wr_n and vram_wren are actually being asserted

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== VRAM Write Signals Monitor ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    // Load DMG boot ROM
    uint8_t dmg_boot[256];
    FILE* f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("ERROR: Cannot open dmg_boot.bin\n");
        return 1;
    }
    fread(dmg_boot, 1, 256, f);
    fclose(f);

    // Reset and download boot ROM
    reset_dut_with_sdram(dut, sdram, 100);

    dut->boot_download = 1;
    tick_with_sdram(dut, sdram);

    for (size_t addr = 0; addr < 256; addr += 2) {
        uint16_t word = dmg_boot[addr];
        if (addr + 1 < 256) {
            word |= (dmg_boot[addr + 1] << 8);
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
    run_cycles_with_sdram(dut, sdram, 200);

    // Load minimal cart
    uint8_t cart[0x150];
    memset(cart, 0, sizeof(cart));
    cart[0x100] = 0x18;
    cart[0x101] = 0xFE;

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

    printf("\n=== Monitoring First 100K Cycles ===\n");

    uint8_t last_ce_cpu = 0;
    uint16_t last_cpu_addr = 0;
    int vram_accesses = 0;
    int cpu_wr_n_low_count = 0;
    int vram_wren_high_count = 0;
    int vram_allowed_count = 0;

    struct VRAMEvent {
        uint64_t cycle;
        uint16_t addr;
        uint8_t cpu_wr_n;
        uint8_t vram_wren;
        uint8_t vram_allow;
        uint8_t lcd_mode;
    };
    std::vector<VRAMEvent> events;

    for (uint64_t cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        // On CPU clock enable
        if (dut->dbg_ce_cpu && !last_ce_cpu) {
            uint16_t addr = dut->dbg_cpu_addr;

            // Check if accessing VRAM ($8000-$9FFF)
            if (addr >= 0x8000 && addr <= 0x9FFF) {
                vram_accesses++;

                // Check signals
                uint8_t wr_n = dut->dbg_cpu_wr_n;
                uint8_t wren = dut->dbg_vram_wren;
                uint8_t allow = dut->dbg_vram_cpu_allow;

                if (!wr_n) cpu_wr_n_low_count++;
                if (wren) vram_wren_high_count++;
                if (allow) vram_allowed_count++;

                if (events.size() < 20) {
                    VRAMEvent e;
                    e.cycle = cycle;
                    e.addr = addr;
                    e.cpu_wr_n = wr_n;
                    e.vram_wren = wren;
                    e.vram_allow = allow;
                    e.lcd_mode = dut->dbg_lcd_mode;
                    events.push_back(e);
                }

                last_cpu_addr = addr;
            }
        }

        last_ce_cpu = dut->dbg_ce_cpu;
    }

    printf("\n=== Results ===\n");
    printf("VRAM accesses: %d\n", vram_accesses);
    printf("cpu_wr_n LOW (write active): %d\n", cpu_wr_n_low_count);
    printf("vram_wren HIGH (write enable): %d\n", vram_wren_high_count);
    printf("vram_cpu_allow HIGH (allowed): %d\n", vram_allowed_count);

    printf("\nFirst 20 VRAM events:\n");
    printf("  # Cycle   Addr   wr_n wren allow mode\n");
    for (size_t i = 0; i < events.size(); i++) {
        printf("  %2zu %6lu 0x%04X   %d    %d     %d    %d\n",
               i, events[i].cycle, events[i].addr,
               events[i].cpu_wr_n, events[i].vram_wren,
               events[i].vram_allow, events[i].lcd_mode);
    }

    printf("\n=== Diagnosis ===\n");
    if (vram_accesses == 0) {
        printf("❌ NO VRAM ACCESSES\n");
    } else {
        printf("✅ VRAM accessed %d times\n", vram_accesses);

        if (cpu_wr_n_low_count == 0) {
            printf("❌ **cpu_wr_n NEVER went LOW** - CPU not asserting write!\n");
        } else {
            printf("✅ cpu_wr_n went LOW %d times\n", cpu_wr_n_low_count);
        }

        if (vram_wren_high_count == 0) {
            printf("❌ **vram_wren NEVER went HIGH** - Write enable NOT working!\n");
        } else {
            printf("✅ vram_wren went HIGH %d times\n", vram_wren_high_count);
        }

        if (vram_allowed_count < vram_accesses / 2) {
            printf("⚠️  Most accesses BLOCKED (vram_cpu_allow=0)\n");
        } else {
            printf("✅ Most accesses ALLOWED\n");
        }
    }

    delete sdram;
    delete dut;

    return 0;
}
