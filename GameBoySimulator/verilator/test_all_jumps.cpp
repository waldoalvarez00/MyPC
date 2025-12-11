#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    // Boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // Test JP (absolute jump)
    rom[0x150] = 0xC3; rom[0x151] = 0x60; rom[0x152] = 0x01;  // JP $0160
    
    // Test JR (relative jump +2)
    rom[0x160] = 0x18; rom[0x161] = 0x02;  // JR +2
    rom[0x162] = 0x76;  // HALT (skip)
    rom[0x163] = 0x00;  // NOP (target)
    
    // Test JR with negative offset
    rom[0x164] = 0x18; rom[0x165] = 0xFE;  // JR -2 (back to 0x164)
    // This creates a loop, so we'll break after detecting it
    
    // Break the loop: use conditional JR that won't be taken
    rom[0x164] = 0x20; rom[0x165] = 0x02;  // JR NZ, +2 (will be taken if Z=0)
    rom[0x166] = 0x76;  // HALT (skip)
    rom[0x167] = 0x3E; rom[0x168] = 0x00;  // LD A, 0 (set Z flag)
    
    rom[0x169] = 0x28; rom[0x16A] = 0x02;  // JR Z, +2 (will be taken since Z=1)
    rom[0x16B] = 0x76;  // HALT (skip)
    rom[0x16C] = 0x00;  // NOP (target)
    rom[0x16D] = 0x76;  // HALT (success marker)

    sdram->loadBinary(0, rom, sizeof(rom));

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t word = minimal_boot[addr];
        if (addr + 1 < 256) word |= (minimal_boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    for (int i = 0; i < 10; i++) {
        dut->ioctl_addr = i;
        dut->ioctl_wr = 1;
        run_cycles_with_sdram(dut, sdram, 64);
        dut->ioctl_wr = 0;
        run_cycles_with_sdram(dut, sdram, 64);
        if (dut->dbg_cart_ready) break;
    }
    dut->ioctl_download = 0;

    bool boot_completed = false;
    bool jp_ok = false, jr_ok = false, jr_nz_ok = false, jr_z_ok = false;
    uint16_t last_pc = 0xFFFF;

    printf("Testing jump instructions...\n");

    for (int cycle = 0; cycle < 300000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
        }

        if (boot_completed && pc != last_pc) {
            if (pc == 0x160 && !jp_ok) {
                jp_ok = true;
                printf("  ✅ JP instruction worked ($0150 → $0160)\n");
            }
            if (pc == 0x163 && !jr_ok) {
                jr_ok = true;
                printf("  ✅ JR +2 worked ($0160 → $0163)\n");
            }
            if (pc == 0x167 && !jr_nz_ok) {
                jr_nz_ok = true;
                printf("  ✅ JR NZ worked ($0164 → $0167)\n");
            }
            if (pc == 0x16C && !jr_z_ok) {
                jr_z_ok = true;
                printf("  ✅ JR Z worked ($0169 → $016C)\n");
            }
            if (pc == 0x16D) {
                printf("\n🎉 All jump tests PASSED!\n");
                break;
            }
            last_pc = pc;
        }
    }

    int result = (jp_ok && jr_ok && jr_nz_ok && jr_z_ok) ? 0 : 1;
    
    if (!jp_ok) printf("  ❌ JP failed\n");
    if (!jr_ok) printf("  ❌ JR +2 failed\n");
    if (!jr_nz_ok) printf("  ❌ JR NZ failed\n");
    if (!jr_z_ok) printf("  ❌ JR Z failed\n");

    delete sdram;
    delete dut;
    return result;
}
