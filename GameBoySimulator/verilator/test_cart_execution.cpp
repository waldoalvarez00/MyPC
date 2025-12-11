#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // REALISTIC latency

    printf("=== Cart ROM Execution Diagnostic ===\n\n");

    // Create minimal boot ROM (NOP padding method like sim_main_gui.cpp)
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);

    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI

    // Pad with NOPs to 0xFC
    while (pc < 0xFC) {
        minimal_boot[pc++] = 0x00;  // NOP
    }

    // Boot ROM disable at end
    minimal_boot[pc++] = 0x3E;  // LD A, $01 at 0xFC
    minimal_boot[pc++] = 0x01;  // Value at 0xFD
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A at 0xFE
    minimal_boot[pc++] = 0x50;  // Address at 0xFF

    printf("Boot ROM: NOP padding to 0xFC, disable at 0xFC-0xFF\n");

    // Create test cart ROM (matches create_test_rom.py)
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // Fill with HALT

    // Entry point
    rom[0x100] = 0x00;  // NOP
    rom[0x101] = 0xC3;  // JP $0150
    rom[0x102] = 0x50;
    rom[0x103] = 0x01;

    // Main program at 0x150 (exactly as in create_test_rom.py)
    pc = 0x150;
    rom[pc++] = 0xF3;  // DI
    rom[pc++] = 0x31; rom[pc++] = 0xFE; rom[pc++] = 0xFF;  // LD SP, $FFFE
    rom[pc++] = 0x3E; rom[pc++] = 0x00;  // LD A, $00
    rom[pc++] = 0xE0; rom[pc++] = 0xFF;  // LDH ($FFFF), A
    rom[pc++] = 0x3E; rom[pc++] = 0x00;  // LD A, $00
    rom[pc++] = 0xE0; rom[pc++] = 0x40;  // LDH ($FF40), A
    rom[pc++] = 0x00;  // NOP at 0x15C
    rom[pc++] = 0x18;  // JR at 0x15D
    rom[pc++] = 0xFD;  // -3 at 0x15E
    // 0x15F will be 0x76 (HALT) from memset

    printf("Cart ROM structure:\n");
    printf("  0x0100-0x0103: NOP, JP $0150\n");
    printf("  0x0150: DI\n");
    printf("  0x0151-0x0153: LD SP,$FFFE\n");
    printf("  0x0154-0x0157: LD A,$00; LDH ($FFFF),A\n");
    printf("  0x0158-0x015B: LD A,$00; LDH ($FF40),A\n");
    printf("  0x015C: NOP\n");
    printf("  0x015D-0x015E: JR -3 (should loop to 0x015C)\n");
    printf("  0x015F: HALT (should never reach)\n\n");

    // Verify ROM bytes
    printf("ROM bytes at 0x150:\n  ");
    for (int i = 0; i < 16; i++) {
        printf("%02X ", rom[0x150 + i]);
    }
    printf("\n\n");

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
    printf("Uploading boot ROM...\n");
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
    printf("Simulating cart download...\n");
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
    printf("Ready\n\n");

    // Run and track PC
    printf("Running simulation...\n\n");

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;
    int cart_pc_changes = 0;
    int loop_count = 0;
    uint16_t last_loop_pc = 0;

    for (int cycle = 0; cycle < 50000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Cycle %d: Boot ROM completed at PC=$%04X\n\n", cycle, pc);
            printf("--- Cart ROM Execution Trace ---\n");
        }

        // Track cart ROM execution
        if (boot_completed && pc != last_pc) {
            cart_pc_changes++;

            // Print first 50 PC changes in cart ROM
            if (cart_pc_changes <= 50) {
                printf("  Cart PC[%2d]: $%04X\n", cart_pc_changes, pc);
            }

            // Detect loop at 0x15C
            if (pc == 0x15C) {
                loop_count++;
                if (loop_count == 1) {
                    printf("\n  ✓ First time at loop (0x015C)\n");
                } else if (loop_count == 2) {
                    printf("  ✓ Looping correctly!\n");
                } else if (loop_count == 10) {
                    printf("  ✓ Loop stable (10 iterations)\n\n");
                }
            }

            // Detect reaching HALT at 0x15F (should never happen)
            if (pc == 0x15F) {
                printf("\n  ❌ ERROR: PC reached HALT at 0x015F!\n");
                printf("     JR instruction did NOT loop correctly\n");
                printf("     Last PC before HALT: $%04X\n", last_pc);
                break;
            }

            // Detect going past loop (0x160+)
            if (pc >= 0x160 && pc < 0x200) {
                printf("\n  ❌ ERROR: PC went past loop to $%04X!\n", pc);
                printf("     This means CPU executed past the JR instruction\n");
                printf("     Last PC: $%04X\n", last_pc);
                break;
            }

            last_pc = pc;
        }

        // Stop after loop is stable
        if (loop_count >= 20) {
            printf("\n=== Test Complete ===\n");
            printf("Loop executed %d times correctly\n", loop_count);
            printf("✅ PASS: Cart ROM executes and loops as expected\n");
            delete sdram;
            delete dut;
            return 0;
        }
    }

    printf("\n=== Test Result ===\n");
    if (loop_count >= 2) {
        printf("✅ PASS: Loop works\n");
    } else if (loop_count == 1) {
        printf("⚠️  WARNING: Reached loop once but didn't iterate\n");
    } else {
        printf("❌ FAIL: Never reached loop at 0x015C\n");
        printf("Last PC: $%04X\n", last_pc);
    }

    delete sdram;
    delete dut;
    return (loop_count < 2) ? 1 : 0;
}
