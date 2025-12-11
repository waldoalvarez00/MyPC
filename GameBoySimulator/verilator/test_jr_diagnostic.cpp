#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== JR vs JP Diagnostic ===\n\n");

    // Minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;  // NOP
    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[pc++] = 0x50;

    // Test ROM: Compare JP and JR side by side
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // Fill with HALT

    // Entry at 0x100
    rom[0x100] = 0xC3;  // JP $0150
    rom[0x101] = 0x50;
    rom[0x102] = 0x01;

    // Test 1: JP (known working)
    rom[0x150] = 0xC3;  // JP $0160
    rom[0x151] = 0x60;
    rom[0x152] = 0x01;
    rom[0x153] = 0x76;  // HALT (should skip)

    // Test 2: JR
    rom[0x160] = 0x18;  // JR +2 (skip 2 bytes to 0x163)
    rom[0x161] = 0x02;  // Offset = +2
    rom[0x162] = 0x76;  // HALT (should skip this)
    rom[0x163] = 0x00;  // NOP (target)
    rom[0x164] = 0x76;  // HALT

    printf("Test ROM:\n");
    printf("  0x0100: JP $0150 (test entry)\n");
    printf("  0x0150: JP $0160 (JP test - known working)\n");
    printf("  0x0160: JR +2 → $0163 (JR test)\n\n");

    printf("ROM bytes:\n");
    printf("  @0x0150: %02X %02X %02X %02X\n", rom[0x150], rom[0x151], rom[0x152], rom[0x153]);
    printf("  @0x0160: %02X %02X %02X %02X\n\n", rom[0x160], rom[0x161], rom[0x162], rom[0x163]);

    // Load into SDRAM
    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize and upload boot ROM
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

    printf("Running simulation...\n\n");

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;
    bool jp_worked = false;
    bool jr_tested = false;
    bool jr_worked = false;
    int pc_count = 0;

    for (int cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;

        if (!boot_completed && !dut->dbg_boot_rom_enabled) {
            boot_completed = true;
            printf("Boot completed\n\n");
        }

        if (boot_completed && pc != last_pc) {
            pc_count++;
            if (pc_count <= 30) {
                printf("  PC[%2d]: $%04X", pc_count, pc);
                if (pc >= 0x100 && pc < 0x200) {
                    printf(" (opcode=0x%02X)", rom[pc]);
                }
                printf("\n");
            }

            // Check JP worked
            if (pc == 0x160) {
                jp_worked = true;
                printf("\n✅ JP worked: Reached 0x0160\n\n");
            }

            // Check if we're testing JR
            if (pc >= 0x160 && pc <= 0x164) {
                jr_tested = true;
                if (pc == 0x162) {
                    printf("\n❌ JR FAILED: Hit HALT at 0x0162!\n");
                    printf("   JR +2 did NOT jump from 0x0160\n\n");
                    break;
                } else if (pc == 0x163) {
                    jr_worked = true;
                    printf("\n✅ JR worked: Reached 0x0163\n\n");
                    break;
                } else if (pc == 0x164) {
                    printf("\n❌ JR FAILED: Reached 0x0164 (skipped target!)\n\n");
                    break;
                }
            }

            last_pc = pc;
        }
    }

    printf("\n=== Results ===\n");
    printf("JP (3-byte): %s\n", jp_worked ? "✅ WORKS" : "❌ FAILS");
    printf("JR (2-byte): %s\n", jr_worked ? "✅ WORKS" : "❌ FAILS");

    if (jp_worked && !jr_worked) {
        printf("\n⚠️  CRITICAL: JP works but JR doesn't!\n");
        printf("   This suggests wait state logic may need adjustment for 2-byte instructions\n");
    }

    delete sdram;
    delete dut;
    return jr_worked ? 0 : 1;
}
