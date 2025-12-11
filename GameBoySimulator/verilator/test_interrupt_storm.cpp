#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== Interrupt Storm Diagnostic Test ===\n\n");

    // Load a simple ROM into SDRAM
    uint8_t rom[32768];
    memset(rom, 0x00, sizeof(rom));  // Fill with NOPs

    // Entry point at 0x100
    rom[0x100] = 0x00;  // NOP
    rom[0x101] = 0xC3;  // JP $0150
    rom[0x102] = 0x50;
    rom[0x103] = 0x01;

    // Nintendo logo (required)
    uint8_t logo[] = {0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B};
    memcpy(&rom[0x104], logo, sizeof(logo));

    // Simple program at 0x150: disable interrupts and loop
    int pc = 0x150;
    rom[pc++] = 0xF3;  // DI (disable interrupts)
    rom[pc++] = 0x00;  // NOP
    rom[pc++] = 0x18;  // JR -2 (loop forever)
    rom[pc++] = 0xFD;

    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    printf("MONITORING CPU STATE FOR INTERRUPT STORM:\n\n");

    uint16_t last_pc = 0xFFFF;
    uint16_t last_sp = 0xFFFF;
    int stuck_count = 0;
    int sp_decrease_count = 0;

    for (int cycle = 0; cycle < 10000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint16_t sp = dut->dbg_cpu_sp;

        // Detect PC stuck at 0x0038-0x003F range (interrupt vectors)
        if (pc >= 0x0038 && pc <= 0x003F) {
            if (pc == last_pc) {
                stuck_count++;
            } else {
                stuck_count = 0;
            }

            if (stuck_count >= 10) {
                printf("Cycle %d: INTERRUPT STORM DETECTED!\n", cycle);
                printf("  PC stuck in range 0x0038-0x003F\n");
                printf("  Current PC: 0x%04X\n", pc);
                printf("  Current SP: 0x%04X\n", sp);
                printf("  Last SP:    0x%04X\n", last_sp);

                // Check interrupt status
                printf("\n  INTERRUPT STATUS:\n");
                printf("    cpu_clken: %d\n", dut->dbg_cpu_clken);
                printf("    ce_cpu: %d\n", dut->dbg_ce_cpu);
                printf("    boot_rom_enabled: %d\n", dut->dbg_boot_rom_enabled);
                printf("    cart_ready: %d\n", dut->dbg_cart_ready);

                // Check what's at this address in memory
                printf("\n  MEMORY AT PC (0x%04X):\n", pc);
                uint8_t byte1 = sdram->read8(pc);
                uint8_t byte2 = sdram->read8(pc + 1);
                printf("    [0x%04X] = 0x%02X\n", pc, byte1);
                printf("    [0x%04X] = 0x%02X\n", pc + 1, byte2);

                // Check interrupt registers (would need debug signals)
                printf("\n  POSSIBLE CAUSES:\n");
                printf("    1. Interrupt enabled but no handler at 0x%04X\n", pc);
                printf("    2. Handler doesn't clear interrupt flag\n");
                printf("    3. Handler doesn't execute RETI\n");
                printf("    4. Continuous interrupt source (VBlank, LCD, etc)\n");

                break;
            }
        }

        // Detect SP decreasing (interrupt pushes)
        if (sp < last_sp) {
            sp_decrease_count++;
            if (sp_decrease_count >= 5) {
                printf("Cycle %d: SP CONTINUOUSLY DECREASING!\n", cycle);
                printf("  SP: 0x%04X -> 0x%04X\n", last_sp, sp);
                printf("  PC: 0x%04X\n", pc);
                printf("  This indicates repeated interrupt calls\n");
                break;
            }
        } else {
            sp_decrease_count = 0;
        }

        last_pc = pc;
        last_sp = sp;
    }

    printf("\n--- Final State ---\n");
    printf("PC: 0x%04X\n", dut->dbg_cpu_addr);
    printf("SP: 0x%04X\n", dut->dbg_cpu_sp);

    delete sdram;
    delete dut;
    return 0;
}
