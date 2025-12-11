// Quick test to check isGBC status
#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    uint8_t dmg_boot[256];
    FILE* f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
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
    run_cycles_with_sdram(dut, sdram, 10);

    printf("=== System Status ===\n");
    printf("isGBC_game: %d\n", dut->dbg_isGBC_game);
    printf("boot_rom_enabled: %d\n", dut->dbg_boot_rom_enabled);

    printf("\nRunning 1M cycles...\n");
    run_cycles_with_sdram(dut, sdram, 1000000);

    printf("After 1M cycles:\n");
    printf("isGBC_game: %d\n", dut->dbg_isGBC_game);
    printf("boot_rom_enabled: %d\n", dut->dbg_boot_rom_enabled);

    delete sdram;
    delete dut;
    return 0;
}
