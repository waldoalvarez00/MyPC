#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>
#include <string.h>

void setup_system(Vtop* dut, MisterSDRAMModel* sdram, uint8_t* rom, size_t rom_size) {
    // Minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;  // LD A, 1
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;  // LDH (FF50), A

    sdram->loadBinary(0, rom, rom_size);

    // Reset
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

    // Trigger cart ready
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

    // Wait for boot to complete
    for (int cycle = 0; cycle < 50000; cycle++) {
        tick_with_sdram(dut, sdram);
        if (!dut->dbg_boot_rom_enabled) break;
    }
}

int main() {
    printf("\n");
    printf("=== DEBUG: 10 Sequential NOPs Test ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    // Entry point
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // 10 NOPs
    for (int i = 0; i < 10; i++) {
        rom[0x150 + i] = 0x00;  // NOP
    }
    rom[0x15A] = 0x76;  // HALT

    printf("ROM Setup:\n");
    printf("  $0100-$0102: JP $0150\n");
    printf("  $0150-$0159: 10 x NOP (0x00)\n");
    printf("  $015A: HALT (0x76)\n");
    printf("  Rest: HALT (0x76)\n\n");

    // Verify ROM contents
    printf("Verifying ROM:\n");
    for (int i = 0x150; i <= 0x15C; i++) {
        printf("  ROM[$%04X] = 0x%02X", i, rom[i]);
        if (i >= 0x150 && i <= 0x159) {
            printf(" (NOP)");
        } else if (i == 0x15A) {
            printf(" (HALT - target)");
        } else {
            printf(" (HALT - fill)");
        }
        printf("\n");
    }
    printf("\n");

    setup_system(dut, sdram, rom, sizeof(rom));

    uint16_t last_pc = 0xFFFF;
    int pc_changes = 0;
    bool boot_completed = false;

    printf("Execution Trace (PC changes only):\n");

    for (int cycle = 0; cycle < 30000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("\n>>> Boot ROM completed at cycle %d <<<\n\n", cycle);
        }

        // Print PC changes in our test region
        if (boot_completed && pc != last_pc) {
            if (pc >= 0x0100 && pc <= 0x0165) {
                printf("  Cycle %6d: PC = $%04X (IR=$%02X)", cycle, pc, ir);

                // Annotate what instruction should be here
                if (pc >= 0x150 && pc <= 0x159) {
                    printf(" [NOP #%d]", pc - 0x150 + 1);
                } else if (pc == 0x15A) {
                    printf(" [HALT - SUCCESS TARGET]");
                } else if (pc == 0x100) {
                    printf(" [JP $0150]");
                }
                printf("\n");

                pc_changes++;

                // If we reach HALT at $015A, success!
                if (pc == 0x15A) {
                    printf("\n✅ SUCCESS: Reached HALT at $015A after 10 NOPs\n");
                    printf("   Total PC changes: %d\n\n", pc_changes);
                    delete sdram;
                    delete dut;
                    return 0;
                }

                // If we hit a HALT before $015A, failure
                if (pc >= 0x150 && pc < 0x15A) {
                    uint8_t opcode = rom[pc];
                    if (opcode == 0x76) {
                        printf("\n❌ FAILURE: Hit unexpected HALT at $%04X\n", pc);
                        printf("   ROM[$%04X] = 0x%02X (should be 0x00 NOP!)\n", pc, opcode);
                        printf("   Total PC changes: %d\n\n", pc_changes);
                        delete sdram;
                        delete dut;
                        return 1;
                    }
                }
            }
            last_pc = pc;
        }
    }

    printf("\n⏱️ TIMEOUT: Did not reach target after 30k cycles\n");
    printf("   Last PC = $%04X\n", last_pc);
    printf("   Total PC changes: %d\n\n", pc_changes);

    delete sdram;
    delete dut;
    return 1;
}
