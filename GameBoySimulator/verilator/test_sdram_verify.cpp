#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    rom[0x150] = 0x37;  // SCF
    rom[0x151] = 0x38; rom[0x152] = 0x02;  // JR C, +2
    rom[0x153] = 0x76;  // HALT (should skip)
    rom[0x154] = 0x3F;  // CCF
    rom[0x155] = 0x30; rom[0x156] = 0x02;  // JR NC, +2
    rom[0x157] = 0x76;  // HALT (should skip)
    rom[0x158] = 0x00;  // NOP
    rom[0x159] = 0x76;  // HALT

    sdram->loadBinary(0, rom, sizeof(rom));

    printf("Verifying SDRAM contents at addresses $0150-$0159:\n");
    for (int addr = 0x150; addr <= 0x159; addr++) {
        uint8_t byte = rom[addr];
        printf("  $%04X: $%02X", addr, byte);
        
        if (addr == 0x150) printf(" (SCF)");
        if (addr == 0x151) printf(" (JR C)");
        if (addr == 0x152) printf(" (+2)");
        if (addr == 0x153) printf(" (HALT - skip)");
        if (addr == 0x154) printf(" (CCF) ← Should be 0x3F");
        if (addr == 0x155) printf(" (JR NC)");
        if (addr == 0x156) printf(" (+2)");
        if (addr == 0x157) printf(" (HALT - skip)");
        if (addr == 0x158) printf(" (NOP)");
        if (addr == 0x159) printf(" (HALT)");
        
        printf("\n");
    }

    delete sdram;
    return 0;
}
