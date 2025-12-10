// Comprehensive diagnostic - run this to see what's happening
#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main() {
    printf("=== GameBoy Diagnostic Check ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

    // Load boot ROM
    uint8_t dmg_boot[256];
    FILE* f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("❌ ERROR: Cannot open dmg_boot.bin\n");
        printf("   Make sure you're running from the verilator directory!\n");
        return 1;
    }
    fread(dmg_boot, 1, 256, f);
    fclose(f);

    reset_dut_with_sdram(dut, sdram, 100);
    dut->boot_download = 1;
    tick_with_sdram(dut, sdram);

    for (size_t addr = 0; addr < 256; addr += 2) {
        uint16_t word = dmg_boot[addr] | (dmg_boot[addr+1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
    }

    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    // Minimal cart
    uint8_t cart[0x8000];
    memset(cart, 0xFF, sizeof(cart));
    cart[0x100] = 0x18;  // JR $FE
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

    printf("Running simulation for 10M cycles...\n");
    printf("Sampling every 100K cycles\n\n");

    uint16_t last_addr = 0;
    int addr_change_count = 0;
    bool boot_completed = false;
    uint64_t boot_complete_cycle = 0;

    int lcd_value_counts[4] = {0, 0, 0, 0};
    int sample_count = 0;

    for (uint64_t cycle = 0; cycle < 10000000; cycle++) {
        tick_with_sdram(dut, sdram);

        // Check for boot ROM completion
        if (!boot_completed && dut->dbg_boot_rom_enabled == 0) {
            boot_completed = true;
            boot_complete_cycle = cycle;
            printf("\n✅✅✅ BOOT ROM DISABLED at cycle %lu! ✅✅✅\n", cycle);
            printf("     This is %.2f ms of game time\n\n", cycle / 4194.304);
        }

        // Sample every 100K cycles
        if (cycle % 100000 == 0) {
            printf("[%7luK] boot=%d addr=$%04X lcd_mode=%d lcd_data=%d",
                   cycle/1000,
                   dut->dbg_boot_rom_enabled,
                   dut->dbg_cpu_addr,
                   dut->dbg_lcd_mode,
                   dut->dbg_lcd_data_gb);

            // Track address changes
            if (dut->dbg_cpu_addr != last_addr) {
                addr_change_count++;
                last_addr = dut->dbg_cpu_addr;
            }

            // Track LCD values
            uint8_t lcd_val = dut->dbg_lcd_data_gb;
            if (lcd_val < 4) {
                lcd_value_counts[lcd_val]++;
                sample_count++;
            }

            // Show indicator if address is changing
            if (cycle > 0 && addr_change_count > (cycle / 100000)) {
                printf(" (CPU active)");
            }

            printf("\n");
        }
    }

    printf("\n=== DIAGNOSTIC RESULTS ===\n\n");

    // Boot ROM Status
    printf("1. BOOT ROM STATUS:\n");
    if (boot_completed) {
        printf("   ✅ Boot ROM COMPLETED\n");
        printf("   ✅ Disabled at cycle: %lu (%.2f ms)\n",
               boot_complete_cycle, boot_complete_cycle / 4194.304);
    } else {
        printf("   ❌ Boot ROM NEVER COMPLETED\n");
        printf("   ❌ Still enabled after 10M cycles\n");
        printf("   ❌ THIS IS THE PROBLEM - FIX DIDN'T WORK!\n");
    }

    // CPU Activity
    printf("\n2. CPU ACTIVITY:\n");
    printf("   Address changes: %d times\n", addr_change_count);
    if (addr_change_count > 50) {
        printf("   ✅ CPU is executing normally\n");
        printf("   ✅ Seeing different addresses is GOOD\n");
    } else {
        printf("   ❌ CPU appears stuck (too few address changes)\n");
    }

    // LCD Output
    printf("\n3. LCD OUTPUT:\n");
    printf("   Pixel value distribution (%d samples):\n", sample_count);
    printf("   Color 0 (white):   %5d (%.1f%%)\n",
           lcd_value_counts[0], 100.0 * lcd_value_counts[0] / sample_count);
    printf("   Color 1 (lt gray): %5d (%.1f%%)\n",
           lcd_value_counts[1], 100.0 * lcd_value_counts[1] / sample_count);
    printf("   Color 2 (dk gray): %5d (%.1f%%)\n",
           lcd_value_counts[2], 100.0 * lcd_value_counts[2] / sample_count);
    printf("   Color 3 (black):   %5d (%.1f%%)\n",
           lcd_value_counts[3], 100.0 * lcd_value_counts[3] / sample_count);

    if (lcd_value_counts[0] == sample_count) {
        printf("   ⚠️  ALL WHITE - VRAM might be cleared to 0x00\n");
    } else if (lcd_value_counts[3] == sample_count) {
        printf("   ⚠️  ALL BLACK - VRAM might be set to 0xFF\n");
    } else if (lcd_value_counts[0] > 0 || lcd_value_counts[1] > 0 ||
               lcd_value_counts[2] > 0) {
        printf("   ✅ MIXED VALUES - Graphics data present!\n");
    }

    printf("\n4. FINAL STATUS:\n");
    printf("   boot_enabled:  %d\n", dut->dbg_boot_rom_enabled);
    printf("   cpu_addr:      $%04X\n", dut->dbg_cpu_addr);
    printf("   lcd_mode:      %d\n", dut->dbg_lcd_mode);
    printf("   lcd_data_gb:   %d\n", dut->dbg_lcd_data_gb);

    printf("\n=== DIAGNOSIS ===\n");
    if (!boot_completed) {
        printf("❌ PRIMARY PROBLEM: Boot ROM never completes\n");
        printf("   → Visual Studio build did NOT pick up the fix\n");
        printf("   → Need to do CLEAN rebuild in Visual Studio\n");
        printf("   → Delete obj_dir and regenerate Verilator files\n");
    } else if (lcd_value_counts[0] == sample_count ||
               lcd_value_counts[3] == sample_count) {
        printf("⚠️  Boot ROM completes, but display shows only one color\n");
        printf("   → VRAM randomization issue (platform-specific)\n");
        printf("   → Boot ROM graphics not persisting\n");
        printf("   → Need to investigate VRAM write/read path\n");
    } else {
        printf("✅ Everything looks good!\n");
        printf("   → Boot ROM completes\n");
        printf("   → CPU executing\n");
        printf("   → Graphics data present\n");
        printf("   → Display should be working!\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
