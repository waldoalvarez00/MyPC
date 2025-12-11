#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main(int argc, char** argv) {
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

    printf("Running 10M cycles...\n");
    
    uint8_t last_ce = 0;
    int boot_disabled_cycle = -1;
    uint16_t pc_when_disabled = 0;
    int lcd_values[4] = {0};
    
    for (uint64_t cycle = 0; cycle < 10000000; cycle++) {
        tick_with_sdram(dut, sdram);
        
        if (dut->dbg_ce_cpu && !last_ce) {
            if (boot_disabled_cycle < 0 && !dut->dbg_boot_rom_enabled) {
                boot_disabled_cycle = cycle;
                pc_when_disabled = dut->dbg_cpu_addr;
                printf("\n✅ Boot ROM DISABLED at cycle %d, PC=$%04X\n", boot_disabled_cycle, pc_when_disabled);
            }
        }
        last_ce = dut->dbg_ce_cpu;
        
        if (cycle % 100000 == 0) {
            uint8_t val = dut->dbg_lcd_data_gb;
            if (val < 4) lcd_values[val]++;
            
            if (cycle % 1000000 == 0) {
                printf("  %luM cycles: PC=$%04X boot=%d lcd=%d\n", 
                       cycle/1000000, dut->dbg_cpu_addr, 
                       dut->dbg_boot_rom_enabled, val);
            }
        }
    }

    printf("\n=== Final Results ===\n");
    printf("Boot ROM disabled: %s\n", boot_disabled_cycle >= 0 ? "YES" : "NO");
    if (boot_disabled_cycle >= 0) {
        printf("  Disabled at cycle: %d\n", boot_disabled_cycle);
        printf("  PC when disabled: $%04X\n", pc_when_disabled);
    }
    
    printf("\nLCD values sampled:\n");
    for (int i = 0; i < 4; i++) {
        printf("  %d: %d samples\n", i, lcd_values[i]);
    }

    delete sdram;
    delete dut;
    return 0;
}
