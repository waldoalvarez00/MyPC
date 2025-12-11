#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== Diagnostic: Why does PC jump to 0x0038? ===\n\n");

    // Create minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);

    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x00;  // LD A, $00
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x40;  // LDH ($FF40), A  ; LCD OFF
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x00;  // LD A, $00
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0xFF;  // LDH ($FFFF), A  ; IE = 0
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;  // LD A, $01
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;  // LDH ($FF50), A  ; Disable boot ROM
    minimal_boot[pc++] = 0xC3; minimal_boot[pc++] = 0x00; minimal_boot[pc++] = 0x01;  // JP $0100

    // Create cart ROM with DETAILED TRACKING
    uint8_t rom[32768];
    memset(rom, 0xFF, sizeof(rom));  // Fill with 0xFF (RST $38) to detect wild jumps

    // Put unique markers at interrupt vectors
    rom[0x00] = 0x00; rom[0x01] = 0x00;  // RST $00: NOP NOP
    rom[0x08] = 0x08; rom[0x09] = 0x08;  // RST $08: marker
    rom[0x10] = 0x10; rom[0x11] = 0x10;  // RST $10: marker
    rom[0x18] = 0x18; rom[0x19] = 0x18;  // RST $18: marker
    rom[0x20] = 0x20; rom[0x21] = 0x20;  // RST $20: marker
    rom[0x28] = 0x28; rom[0x29] = 0x28;  // RST $28: marker
    rom[0x30] = 0x30; rom[0x31] = 0x30;  // RST $30: marker
    rom[0x38] = 0x38; rom[0x39] = 0x38;  // RST $38: marker (THIS IS WHERE PC GETS STUCK)

    // Interrupt vectors with RETI
    rom[0x40] = 0xD9;  // VBlank: RETI
    rom[0x48] = 0xD9;  // LCD STAT: RETI
    rom[0x50] = 0xD9;  // Timer: RETI
    rom[0x58] = 0xD9;  // Serial: RETI
    rom[0x60] = 0xD9;  // Joypad: RETI

    // Entry point
    rom[0x100] = 0x00;  // NOP
    rom[0x101] = 0xC3;  // JP $0150
    rom[0x102] = 0x50;
    rom[0x103] = 0x01;

    // Nintendo logo
    uint8_t logo[] = {0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B};
    memcpy(&rom[0x104], logo, sizeof(logo));

    // Main program at 0x150
    pc = 0x150;
    rom[pc++] = 0xF3;  // DI
    rom[pc++] = 0x31; rom[pc++] = 0xFE; rom[pc++] = 0xFF;  // LD SP, $FFFE
    rom[pc++] = 0x3E; rom[pc++] = 0x00;  // LD A, $00
    rom[pc++] = 0xE0; rom[pc++] = 0x40;  // LDH ($FF40), A  ; LCD OFF
    rom[pc++] = 0x3E; rom[pc++] = 0x00;  // LD A, $00
    rom[pc++] = 0xE0; rom[pc++] = 0xFF;  // LDH ($FFFF), A  ; IE = 0
    rom[pc++] = 0x00;  // NOP
    rom[pc++] = 0x18; rom[pc++] = 0xFD;  // JR -3 (loop)

    printf("ROM created with markers:\n");
    printf("  Addresses 0x00-0x38: Unique markers (0x00, 0x08, 0x10, ..., 0x38)\n");
    printf("  Address 0x0038: 0x%02X (marker for RST $38)\n", rom[0x38]);
    printf("  Rest filled with 0xFF (RST $38 opcode) to detect wild jumps\n\n");

    // Load into SDRAM
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

    printf("Running simulation with PC tracking...\n\n");

    uint16_t pc_history[100];
    int hist_idx = 0;
    uint16_t last_pc = 0xFFFF;
    int stuck_count = 0;

    for (int cycle = 0; cycle < 10000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint16_t sp = dut->dbg_cpu_sp;

        // Track PC history
        pc_history[hist_idx] = pc;
        hist_idx = (hist_idx + 1) % 100;

        // Detect jump to 0x0038
        if (pc == 0x0038) {
            if (last_pc != 0x0038) {
                printf("Cycle %d: ⚠️  PC JUMPED TO 0x0038!\n", cycle);
                printf("  Previous PC: 0x%04X\n", last_pc);
                printf("  Current SP: 0x%04X\n", sp);
                printf("  boot_rom_enabled: %d\n", dut->dbg_boot_rom_enabled);

                // Show PC history (last 20 PCs)
                printf("\n  PC History (last 20):\n");
                for (int i = 0; i < 20; i++) {
                    int idx = (hist_idx + 100 - 20 + i) % 100;
                    printf("    [-%d] 0x%04X", 19-i, pc_history[idx]);
                    if (i == 19) printf(" <-- Current");
                    printf("\n");
                }

                // Check what instruction caused the jump
                printf("\n  Instruction at last PC (0x%04X):\n", last_pc);
                printf("    [0x%04X] = 0x%02X\n", last_pc, sdram->read8(last_pc));
                printf("    [0x%04X] = 0x%02X\n", last_pc+1, sdram->read8(last_pc+1));
                printf("    [0x%04X] = 0x%02X\n", last_pc+2, sdram->read8(last_pc+2));

                printf("\n  Stack contents (SP = 0x%04X):\n", sp);
                for (int i = 0; i < 8; i++) {
                    printf("    [0x%04X] = 0x%02X\n", sp + i, sdram->read8(sp + i));
                }

                // Check if this is a RST instruction or interrupt
                uint8_t opcode = sdram->read8(last_pc);
                if (opcode == 0xFF) {
                    printf("\n  CAUSE: RST $38 instruction (0xFF) at 0x%04X\n", last_pc);
                    printf("  This is likely wild memory access - code jumped to uninitialized area\n");
                } else if (opcode >= 0xC7 && opcode <= 0xFF && (opcode & 0xC7) == 0xC7) {
                    printf("\n  CAUSE: RST instruction (0x%02X) at 0x%04X\n", opcode, last_pc);
                } else {
                    printf("\n  CAUSE: Unknown - not a RST instruction\n");
                    printf("  Might be interrupt or hardware issue\n");
                }

                break;
            }

            stuck_count++;
            if (stuck_count >= 10) {
                printf("\nCycle %d: PC STUCK at 0x0038 for 10+ cycles\n", cycle);
                break;
            }
        } else {
            stuck_count = 0;
        }

        last_pc = pc;
    }

    printf("\n--- Diagnostic Complete ---\n");

    delete sdram;
    delete dut;
    return 0;
}
