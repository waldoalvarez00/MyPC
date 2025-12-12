#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>
#include <string.h>

void setup_system(Vtop* dut, MisterSDRAMModel* sdram, uint8_t* rom, size_t rom_size) {
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;  // LD A, 1
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;  // LDH (FF50), A

    sdram->loadBinary(0, rom, rom_size);

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

    for (int cycle = 0; cycle < 50000; cycle++) {
        tick_with_sdram(dut, sdram);
        if (!dut->dbg_boot_rom_enabled) break;
    }
}

int main() {
    printf("\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("   JR MCycle Analysis - Comparing Working vs Broken Cases\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    printf("After MCycles fix, we now have:\n");
    printf("  ✅ Test 7: JR C when carry=0 (don't jump) - PASSES\n");
    printf("  ❌ Test 6: JR C when carry=1 (DO jump) - FAILS\n");
    printf("  ❌ Test 3: JR unconditional (always jump) - FAILS\n\n");
    printf("This test will trace execution to understand why jumping still fails.\n\n");

    // Test unconditional JR
    {
        printf("[ TEST ] Unconditional JR +2\n");
        printf("─────────────────────────────────────────────────────────────\n");

        Vtop* dut = new Vtop;
        MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
        sdram->cas_latency = 2;

        uint8_t rom[32768];
        memset(rom, 0x76, sizeof(rom));
        rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;
        rom[0x150] = 0x18; rom[0x151] = 0x02;  // JR +2
        rom[0x152] = 0x00;  // Should skip
        rom[0x153] = 0x00;  // Should skip
        rom[0x154] = 0x76;  // HALT target

        printf("Expected: PC $0150 (JR) -> $0154 (HALT)\n");
        printf("ROM: $0150=0x18, $0151=0x02, $0152-$0153=NOP, $0154=HALT\n\n");

        setup_system(dut, sdram, rom, sizeof(rom));

        uint16_t last_pc = 0xFFFF;
        bool in_region = false;

        for (int cycle = 0; cycle < 30000; cycle++) {
            tick_with_sdram(dut, sdram);
            uint16_t pc = dut->dbg_cpu_addr;

            if (pc >= 0x0150 && pc <= 0x0155 && !dut->dbg_boot_rom_enabled) {
                if (pc != last_pc) {
                    printf("  PC=$%04X", pc);
                    if (pc == 0x150) printf(" [JR +2]");
                    else if (pc == 0x151) printf(" [offset]");
                    else if (pc == 0x152) printf(" [NOP-SKIP!]");
                    else if (pc == 0x153) printf(" [NOP-SKIP!]");
                    else if (pc == 0x154) printf(" [HALT ✓]");
                    printf("\n");

                    if (pc == 0x154) {
                        printf("\n✅ JR WORKS!\n\n");
                        break;
                    }
                    if (pc == 0x152 || pc == 0x153) {
                        printf("\n❌ JR FAILED - executed skipped bytes\n\n");
                        break;
                    }
                    last_pc = pc;
                }
            }
        }

        delete sdram;
        delete dut;
    }

    return 0;
}
