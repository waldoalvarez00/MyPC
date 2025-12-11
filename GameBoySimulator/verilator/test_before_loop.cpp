#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Trace Before Logo Loop ===\n\n");

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

    printf("Monitoring PC from reset until loop entry...\n\n");

    bool hit_loop = false;

    for (int i = 0; i < 500; i++) {
        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t ir = dut->dbg_cpu_ir;

        // Show every instruction until we hit the loop
        if (i % 20 == 0 || pc >= 0x0004) {
            printf("  [%6d] PC=$%04X IR=$%02X HL=$%04X\n", i, pc, ir, hl);
        }

        if (pc == 0x0006) {
            printf("\n*** REACHED LOOP at cycle %d ***\n", i);
            printf("    HL=$%04X (should be pointing to Nintendo logo in ROM)\n", hl);
            printf("    Expected: HL should point to $0104 (logo data in cart header)\n");
            hit_loop = true;
            break;
        }

        tick_with_sdram(dut, sdram);
    }

    if (hit_loop) {
        printf("\nBoot ROM disassembly (first instructions):\n");
        printf("  $0000: NOP or LD SP, xxxx (setup)\n");
        printf("  $0003-$0005: LD HL, $0104 (point to logo in cart header)\n");
        printf("  $0006: LD DE, $8010 (VRAM destination for logo)\n");
        printf("\nThe boot ROM should copy Nintendo logo from cart at $0104-$0133\n");
        printf("to VRAM at $8010-$808F for display.\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
