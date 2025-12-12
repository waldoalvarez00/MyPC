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
    minimal_boot[pc++] = 0xF3;
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;

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
    printf("   IR Register and MCycle Analysis for JR Instruction\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;
    rom[0x150] = 0x18; rom[0x151] = 0x02;  // JR +2
    rom[0x152] = 0x00;
    rom[0x153] = 0x00;
    rom[0x154] = 0x76;

    printf("ROM Setup:\n");
    printf("  $0150: 0x18 (JR opcode)\n");
    printf("  $0151: 0x02 (offset)\n");
    printf("  $0152-$0153: NOP\n");
    printf("  $0154: HALT\n\n");

    setup_system(dut, sdram, rom, sizeof(rom));

    uint16_t last_pc = 0xFFFF;
    uint8_t last_ir = 0xFF;
    bool in_region = false;
    int sample_count = 0;

    printf("Detailed Trace at PC=$0150 (JR instruction):\n");
    printf("────────────────────────────────────────────────────────────\n");
    printf("  Cycle    PC     IR   MCycle  Description\n");
    printf("────────────────────────────────────────────────────────────\n");

    for (int cycle = 0; cycle < 30000; cycle++) {
        tick_with_sdram(dut, sdram);
        
        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_enabled && pc >= 0x0150 && pc <= 0x0155) {
            // Print every cycle when at PC=$0150
            if (pc == 0x150 || (in_region && sample_count < 50)) {
                printf("  %6d  $%04X  $%02X    ", cycle, pc, ir);
                
                // Try to decode MCycle from context (this is approximate)
                if (pc != last_pc) {
                    printf("M1?     [New PC - likely M1]");
                } else if (ir != last_ir) {
                    printf("M2?     [IR changed]");
                } else {
                    printf("M2/M3?  [Same IR]");
                }
                printf("\n");
                
                sample_count++;
                in_region = true;
            }

            // Track PC changes
            if (pc != last_pc) {
                if (pc == 0x152 || pc == 0x153) {
                    printf("\n❌ FAILED: JR did not jump - reached skip region\n");
                    printf("   IR during execution never contained 0x18!\n\n");
                    break;
                }
                if (pc == 0x154) {
                    printf("\n✅ SUCCESS: JR jumped correctly!\n\n");
                    break;
                }
            }

            last_pc = pc;
            last_ir = ir;
        }

        if (in_region && sample_count >= 50) break;
    }

    printf("\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Analysis: The IR register must contain 0x18 for the microcode\n");
    printf("case statement to match and set MCycles=3. If IR never contains\n");
    printf("the JR opcode, the microcode cannot execute the jump logic.\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    delete sdram;
    delete dut;
    return 0;
}
