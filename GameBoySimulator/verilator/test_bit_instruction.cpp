#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);

    printf("=== BIT Instruction Test ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);

    printf("Boot ROM instructions at logo copy loop:\n");
    printf("  $0006: %02X       = LD (HL+), A\n", boot_rom[0x0006]);
    printf("  $0007: %02X %02X    = BIT instruction\n", boot_rom[0x0007], boot_rom[0x0008]);
    printf("  $0009: %02X %02X    = JR Z, $0006\n", boot_rom[0x0009], boot_rom[0x000A]);

    // Decode CB 6C
    uint8_t cb_opcode = boot_rom[0x0008];
    int bit_num = (cb_opcode >> 3) & 7;
    int reg_num = cb_opcode & 7;
    const char* regs[] = {"B", "C", "D", "E", "H", "L", "(HL)", "A"};
    printf("  CB %02X = BIT %d, %s\n\n", cb_opcode, bit_num, regs[reg_num]);

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

    printf("Monitoring BIT instruction execution:\n\n");

    uint16_t last_pc = 0;
    int bit_executions = 0;

    for (int i = 0; i < 50000; i++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;

        // When PC is at $0007 (BIT instruction)
        if (pc == 0x0007 && last_pc != 0x0007 && bit_executions < 20) {
            bit_executions++;

            // Get HL register value (from CPU internals)
            // Note: We'd need to add debug signals for HL, but for now monitor VRAM addr as proxy
            printf("  [%6d] At BIT instruction #%d: F=$%02X\n",
                   i, bit_executions, dut->dbg_cpu_f);
        }

        // When PC is at $0009 (JR Z instruction) - check if Zero flag causes jump
        if (pc == 0x0009 && last_pc != 0x0009 && bit_executions <= 20) {
            uint8_t flags = dut->dbg_cpu_f;
            bool zero_flag = (flags & 0x80) != 0;  // Bit 7 is Zero flag

            printf("  [%6d] At JR Z: F=$%02X Z=%d (will %s)\n",
                   i, flags, zero_flag ? 1 : 0, zero_flag ? "jump to $0006" : "continue to $000B");
        }

        // Check if we ever get past $000B
        if (pc >= 0x000C && last_pc < 0x000C) {
            printf("\n  [%6d] *** EXITED LOOP! PC=$%04X ***\n\n", i, pc);

            // Show next few PC changes
            for (int j = 0; j < 20; j++) {
                uint16_t old_pc = dut->dbg_cpu_pc;
                tick_with_sdram(dut, sdram);
                if (dut->dbg_cpu_pc != old_pc) {
                    printf("  [%6d] PC=$%04X\n", i+j, dut->dbg_cpu_pc);
                }
            }
            break;
        }

        last_pc = pc;

        if (bit_executions >= 20) break;
    }

    printf("\n--- Results ---\n");
    printf("BIT executions: %d\n", bit_executions);
    printf("Final PC: $%04X\n", dut->dbg_cpu_pc);

    if (dut->dbg_cpu_pc < 0x000C) {
        printf("✗ Loop did not exit\n");
    } else {
        printf("✓ Loop exited successfully\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
