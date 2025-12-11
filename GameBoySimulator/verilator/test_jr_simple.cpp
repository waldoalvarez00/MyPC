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
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;  // NOP
    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[pc++] = 0x50;

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // Fill with HALT

    rom[0x100] = 0xC3;  // JP $0150
    rom[0x101] = 0x50;
    rom[0x102] = 0x01;

    rom[0x150] = 0xC3;  // JP $0160
    rom[0x151] = 0x60;
    rom[0x152] = 0x01;

    rom[0x160] = 0x18;  // JR +2
    rom[0x161] = 0x02;  // Offset
    rom[0x162] = 0x10;  // STOP (should skip)
    rom[0x163] = 0x00;  // NOP (SUCCESS target)
    rom[0x164] = 0x10;  // STOP (SUCCESS marker)

    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    // Upload boot ROM
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

    // Simulate cart download
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
    bool found_stop_at_164 = false;
    bool found_stop_at_162 = false;

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot completed at cycle %d\n", cycle);
        }

        if (boot_completed) {
            // Check for STOP at 0x164 (SUCCESS)
            if (pc == 0x164 && !found_stop_at_164) {
                found_stop_at_164 = true;
                printf("\n✅ SUCCESS: Reached $0164 (STOP after NOP)\n");
                printf("   JR instruction jumped correctly from $0160 to $0163\n");
                break;
            }

            // Check for STOP at 0x162 (FAILURE)
            if (pc == 0x162 && !found_stop_at_162) {
                found_stop_at_162 = true;
                printf("\n❌ FAILURE: Reached $0162 (STOP - should have been skipped)\n");
                printf("   JR instruction did NOT jump - executed byte-by-byte\n");
                break;
            }
        }
    }

    if (!found_stop_at_164 && !found_stop_at_162) {
        printf("\n⚠️  TIMEOUT: Neither success nor failure detected\n");
    }

    delete sdram;
    delete dut;

    return found_stop_at_164 ? 0 : 1;
}
