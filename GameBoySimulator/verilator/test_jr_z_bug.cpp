#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    // MisterSDRAMModel ctor takes size in MB (not bytes).
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== JR Z Conditional Jump Bug Test ===\n\n");

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

    printf("Monitoring JR Z at $0009:\n");
    printf("Expected: Jump to $0006 when Z=1, continue to $000B when Z=0\n\n");

    uint16_t last_pc = 0;
    int jr_executions = 0;

    for (int i = 0; i < 50000; i++) {
        uint16_t pc = dut->dbg_cpu_pc;

        tick_with_sdram(dut, sdram);

        // Detect PC change from $0009
        if (last_pc == 0x0009 && pc != 0x0009 && jr_executions < 20) {
            jr_executions++;

            uint8_t flags = dut->dbg_cpu_f;
            bool zero_flag = (flags & 0x80) != 0;

            printf("  [%6d] JR Z executed: F=$%02X Z=%d, jumped to PC=$%04X ",
                   i, flags, zero_flag ? 1 : 0, pc);

            if (zero_flag && pc == 0x0006) {
                printf("✓ Correct (Z=1, jumped)\n");
            } else if (!zero_flag && pc == 0x000B) {
                printf("✓ Correct (Z=0, didn't jump)\n");
            } else if (!zero_flag && pc == 0x0006) {
                printf("✗ BUG! (Z=0 but jumped anyway)\n");
            } else {
                printf("? Unexpected (jumped to $%04X)\n", pc);
            }

            // If we ever get to $000B, show what happens next
            if (pc == 0x000B) {
                printf("\n  *** Loop exited! Continuing execution... ***\n");
                for (int j = 0; j < 50; j++) {
                    uint16_t old_pc = dut->dbg_cpu_pc;
                    tick_with_sdram(dut, sdram);
                    if (dut->dbg_cpu_pc != old_pc) {
                        printf("  [%6d] PC=$%04X\n", i+j, dut->dbg_cpu_pc);
                    }
                }
                break;
            }
        }

        last_pc = pc;

        if (jr_executions >= 20) break;
    }

    printf("\n--- Results ---\n");
    printf("JR Z executions: %d\n", jr_executions);
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);

    if (dut->dbg_cpu_pc < 0x000C) {
        printf("\n✗ BUG CONFIRMED: JR Z jumps even when Z=0\n");
        printf("  This is a CPU core bug in the TV80 implementation\n");
    } else {
        printf("\n✓ JR Z working correctly\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
