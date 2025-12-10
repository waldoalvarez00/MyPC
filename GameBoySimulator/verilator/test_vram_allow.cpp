// Test to monitor vram_cpu_allow and VRAM writes
// Purpose: See if boot ROM VRAM writes are being blocked

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== VRAM CPU Allow Monitoring Test ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

    // Load DMG boot ROM (the real one)
    uint8_t dmg_boot[256];
    FILE* f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("ERROR: Cannot open dmg_boot.bin\n");
        return 1;
    }
    fread(dmg_boot, 1, 256, f);
    fclose(f);

    printf("Loaded DMG boot ROM (256 bytes)\n");

    // Reset
    reset_dut_with_sdram(dut, sdram, 100);

    // Download boot ROM (16-bit words)
    printf("Downloading boot ROM...\n");
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
    int vram_write_attempts = 0;
    int vram_allowed_writes = 0;
    int vram_blocked_writes = 0;
    uint8_t last_lcd_mode = 0xff;
    int mode_changes = 0;

    // Track first few VRAM writes
    struct VRAMWrite {
        uint64_t cycle;
        uint16_t addr;
        uint8_t mode;
        bool allowed;
    };
    std::vector<VRAMWrite> writes;

    for (uint64_t cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        // Track LCD mode changes
        if (dut->dbg_lcd_mode != last_lcd_mode) {
            mode_changes++;
            last_lcd_mode = dut->dbg_lcd_mode;
        }

        // On CPU clock enable
        if (dut->dbg_ce_cpu && !last_ce_cpu) {
            uint16_t addr = dut->dbg_cpu_addr;

            // Check if accessing VRAM ($8000-$9FFF)
            if (addr >= 0x8000 && addr <= 0x9FFF) {
                vram_write_attempts++;

                // Note: We can't directly see vram_cpu_allow from testbench,
                // but we can infer it from lcd_mode:
                // vram_cpu_allow = (lcd_mode != 3)
                bool allowed = (dut->dbg_lcd_mode != 3);

                if (allowed) {
                    vram_allowed_writes++;
                } else {
                    vram_blocked_writes++;
                }

                if (writes.size() < 20) {
                    VRAMWrite w;
                    w.cycle = cycle;
                    w.addr = addr;
                    w.mode = dut->dbg_lcd_mode;
                    w.allowed = allowed;
                    writes.push_back(w);
                }

                last_cpu_addr = addr;
            }
        }

        last_ce_cpu = dut->dbg_ce_cpu;
    }

    printf("\n=== Results ===\n");
    printf("LCD mode changes: %d\n", mode_changes);
    printf("VRAM access attempts: %d\n", vram_write_attempts);
    printf("VRAM allowed (mode != 3): %d\n", vram_allowed_writes);
    printf("VRAM blocked (mode == 3): %d\n", vram_blocked_writes);

    printf("\nFirst 20 VRAM accesses:\n");
    for (size_t i = 0; i < writes.size(); i++) {
        printf("  [%2zu] cycle=%6lu addr=0x%04X mode=%d %s\n",
               i, writes[i].cycle, writes[i].addr, writes[i].mode,
               writes[i].allowed ? "ALLOWED" : "BLOCKED");
    }

    printf("\n=== Analysis ===\n");
    if (vram_write_attempts == 0) {
        printf("❌ NO VRAM ACCESSES - Boot ROM not executing or not reaching VRAM writes\n");
    } else {
        printf("✅ Boot ROM accessing VRAM (%d attempts)\n", vram_write_attempts);

        if (vram_blocked_writes > vram_allowed_writes * 2) {
            printf("⚠️  Most writes BLOCKED (mode 3) - Bad timing\n");
        } else {
            printf("✅ Most writes ALLOWED\n");
        }
    }

    delete sdram;
    delete dut;

    return 0;
}
