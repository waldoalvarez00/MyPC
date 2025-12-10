#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

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

    printf("Monitoring for $FF50 writes (10M cycles)...\n");
    
    int ff50_access_count = 0;
    int ff50_write_count = 0;
    
    for (uint64_t cycle = 0; cycle < 10000000; cycle++) {
        tick_with_sdram(dut, sdram);
        
        if (dut->dbg_cpu_addr == 0xFF50) {
            ff50_access_count++;
            
            if (!dut->dbg_cpu_wr_n) {
                ff50_write_count++;
                printf("\n✅ WRITE to $FF50 at cycle %lu!\n", cycle);
                printf("   boot_enabled=%d\n", dut->dbg_boot_rom_enabled);
                
                // Run a bit more to see if boot ROM disables
                for (int i = 0; i < 1000; i++) {
                    tick_with_sdram(dut, sdram);
                    if (!dut->dbg_boot_rom_enabled) {
                        printf("   ✅ Boot ROM DISABLED after %d more cycles!\n", i);
                        printf("   Final PC: $%04X\n", dut->dbg_cpu_addr);
                        
                        delete sdram;
                        delete dut;
                        return 0;
                    }
                }
                
                printf("   ❌ Boot ROM still enabled after 1000 cycles\n");
            }
        }
        
        if (cycle % 1000000 == 0) {
            printf(".");
            fflush(stdout);
        }
    }

    printf("\n\n=== Results ===\n");
    printf("$FF50 accesses: %d\n", ff50_access_count);
    printf("$FF50 writes: %d\n", ff50_write_count);
    printf("Boot ROM state: %s\n", dut->dbg_boot_rom_enabled ? "ENABLED" : "disabled");

    if (ff50_write_count == 0) {
        printf("\n❌ PROBLEM: Boot ROM NEVER wrote to $FF50!\n");
        printf("   This means boot ROM didn't complete its sequence\n");
        printf("   Boot ROM might be stuck in a loop or crashed\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
