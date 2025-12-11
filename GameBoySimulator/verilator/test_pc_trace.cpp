#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== Detailed PC Trace Around JR Z ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM
    dut->boot_download = 1;
    for (int i = 0; i < 256; i += 2) {
        dut->boot_addr = i;
        dut->boot_data = boot_rom[i] | (boot_rom[i+1] << 8);
        dut->boot_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;

    // Simulate cart
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Boot ROM instructions:\n");
    printf("  $0006: 22       = LD (HL+), A\n");
    printf("  $0007: CB 6C    = BIT 5, H\n");
    printf("  $0009: 28 FB    = JR Z, -5  (jump to $0006 if Z=1)\n");
    printf("  $000B: 3E 80    = LD A, $80\n\n");

    printf("PC trace showing execution around loop (showing every PC change for 3 loops):\n\n");

    uint16_t last_pc = 0xFFFF;
    int loops = 0;
    bool in_loop = false;

    for (int i = 0; i < 50000; i++) {
        uint16_t pc = dut->dbg_cpu_pc;

        if (pc != last_pc) {
            // Detect loop entry
            if (pc == 0x0006 && !in_loop) {
                loops++;
                in_loop = true;
                printf("--- Loop #%d ---\n", loops);
            }

            // Detect loop exit
            if (pc >= 0x000B && in_loop) {
                in_loop = false;
                printf("  [%6d] PC=$%04X *** EXITED LOOP ***\n", i, pc);

                // Show next few instructions
                for (int j = 0; j < 30; j++) {
                    uint16_t old_pc = dut->dbg_cpu_pc;
                    tick_with_sdram(dut, sdram);
                    if (dut->dbg_cpu_pc != old_pc) {
                        printf("  [%6d] PC=$%04X\n", i+j, dut->dbg_cpu_pc);
                    }
                }
                break;
            }

            // Show PC changes while in loop (first 3 loops only)
            if (loops <= 3) {
                uint8_t flags = dut->dbg_cpu_f;
                printf("  [%6d] PC=$%04X F=$%02X", i, pc, flags);

                if (pc == 0x0006) printf(" (LD (HL+),A)");
                if (pc == 0x0007) printf(" (BIT 5,H - will set flags)");
                if (pc == 0x0009) printf(" (JR Z - Z=%d)", (flags & 0x80) ? 1 : 0);
                if (pc == 0x000A) printf(" (offset byte?!)");
                if (pc == 0x000B) printf(" (next instr - loop exited!)");

                printf("\n");
            }

            last_pc = pc;
        }

        tick_with_sdram(dut, sdram);

        if (loops > 3 && !in_loop) break;
    }

    printf("\n--- Results ---\n");
    printf("Completed loops: %d\n", loops);
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);

    delete sdram;
    delete dut;
    return 0;
}
