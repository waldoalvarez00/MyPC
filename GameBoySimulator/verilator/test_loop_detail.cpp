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

    printf("=== Detailed Loop Analysis ($0006-$000C) ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);

    // Print disassembly of the critical loop region
    printf("Boot ROM bytes at loop region:\n");
    for (int i = 0x0006; i <= 0x000C; i++) {
        printf("  $%04X: %02X\n", i, boot_rom[i]);
    }
    printf("\n");

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

    printf("Monitoring every cycle in the loop region...\n\n");

    bool in_loop_region = false;
    int cycles_in_loop = 0;

    for (int i = 0; i < 30000; i++) {
        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t f = dut->dbg_cpu_f;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t data_out = dut->dbg_cpu_do;
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;

        if (pc >= 0x0006 && pc <= 0x000C) {
            if (!in_loop_region) {
                in_loop_region = true;
                printf("=== ENTERED LOOP REGION at cycle %d ===\n", i);
            }

            cycles_in_loop++;
            if (cycles_in_loop <= 200) {
                printf("  [%6d] PC=$%04X IR=$%02X HL=$%04X F=$%02X (Z=%d C=%d) addr=$%04X wr_n=%d\n",
                       i, pc, ir, hl, f,
                       (f >> 7) & 1,  // Z flag
                       (f >> 4) & 1,  // C flag
                       addr, wr_n);
            }
        } else if (in_loop_region) {
            printf("=== EXITED LOOP REGION at cycle %d to PC=$%04X ===\n", i, pc);
            printf("    Final HL=$%04X, F=$%02X (Z=%d C=%d)\n",
                   hl, f, (f >> 7) & 1, (f >> 4) & 1);
            printf("    Total cycles in loop: %d\n\n", cycles_in_loop);
            in_loop_region = false;

            // Only show first exit
            break;
        }

        tick_with_sdram(dut, sdram);
    }

    printf("\nBoot ROM instructions at loop (based on observed opcodes):\n");
    printf("  $0006: LD A, [HL+]     - Load from HL, increment HL\n");
    printf("  $0007: LD [DE], A      - Store to DE\n");
    printf("  $0008: INC DE          - Increment DE\n");
    printf("  $0009: BIT 5, H        - Test bit 5 of H register\n");
    printf("  $000B: JR Z, -5        - Jump back if Z=1 (bit was 0)\n");
    printf("\nLoop should continue while H < $80 (until HL >= $8000)\n");
    printf("Loop started with HL=$0000, should run until HL=$8000\n");

    delete sdram;
    delete dut;
    return 0;
}
