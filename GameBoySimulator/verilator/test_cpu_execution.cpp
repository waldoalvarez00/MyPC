// Test CPU execution path - debug why CPU is at $7xxx
#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== CPU Execution Diagnostic ===\n\n");

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
    size_t boot_read = fread(dmg_boot, 1, 256, f);
    fclose(f);
    printf("Loaded %zu bytes of boot ROM\n", boot_read);

    // Print first 16 bytes of boot ROM
    printf("Boot ROM first 16 bytes: ");
    for (int i = 0; i < 16; i++) {
        printf("%02X ", dmg_boot[i]);
    }
    printf("\n\n");

    // Reset system
    printf("Resetting system...\n");
    reset_dut_with_sdram(dut, sdram, 100);

    // Download boot ROM
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
    printf("Boot ROM download complete\n");

    run_cycles_with_sdram(dut, sdram, 200);

    // Load minimal cart
    printf("\nLoading minimal cart...\n");
    uint8_t cart[0x8000];
    memset(cart, 0xFF, sizeof(cart));

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
    printf("Cart upload complete\n\n");

    run_cycles_with_sdram(dut, sdram, 10);

    printf("=== Monitoring CPU (100K cycles) ===\n\n");

    uint16_t last_addr = 0;
    uint8_t last_ce = 0;
    int instruction_count = 0;
    int boot_rom_count = 0;
    int vram_write_count = 0;

    for (uint64_t cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_ce_cpu && !last_ce) {
            uint16_t addr = dut->dbg_cpu_addr;
            
            if (dut->dbg_boot_rom_enabled) boot_rom_count++;
            if (addr >= 0x8000 && addr <= 0x9FFF && !dut->dbg_cpu_wr_n) vram_write_count++;

            if (instruction_count < 30) {
                printf("[%5d] PC=$%04X boot=%d rd=%d wr=%d\n", 
                       instruction_count, addr, dut->dbg_boot_rom_enabled,
                       dut->dbg_cpu_rd_n, dut->dbg_cpu_wr_n);
            }

            instruction_count++;
            last_addr = addr;
        }

        last_ce = dut->dbg_ce_cpu;
    }

    printf("\n=== Results ===\n");
    printf("CPU cycles: %d\n", instruction_count);
    printf("Boot ROM enabled: %d cycles\n", boot_rom_count);
    printf("VRAM writes: %d\n", vram_write_count);
    printf("Last PC: $%04X\n", last_addr);

    printf("\n=== Diagnosis ===\n");
    if (instruction_count == 0) {
        printf("❌ CPU NOT EXECUTING!\n");
    } else if (last_addr >= 0x7000) {
        printf("❌ CPU at $%04X - should be $0100!\n", last_addr);
    } else if (last_addr == 0x0100 || last_addr == 0x0101) {
        printf("✅ CPU at cart entry ($%04X)\n", last_addr);
    }

    if (vram_write_count > 0) {
        printf("✅ %d VRAM writes\n", vram_write_count);
    } else {
        printf("❌ NO VRAM writes!\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
