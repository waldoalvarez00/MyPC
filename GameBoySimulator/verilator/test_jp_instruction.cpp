#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // REALISTIC latency

    printf("=== JP Instruction Execution Test ===\n\n");

    // Create minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);

    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI

    while (pc < 0xFC) {
        minimal_boot[pc++] = 0x00;  // NOP
    }

    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[pc++] = 0x50;

    // Create cart ROM with JUST a JP instruction at 0x100
    uint8_t rom[32768];
    memset(rom, 0x00, sizeof(rom));  // Fill with NOP

    // Put JP $0150 at 0x100
    rom[0x100] = 0xC3;  // JP opcode
    rom[0x101] = 0x50;  // Low byte of $0150
    rom[0x102] = 0x01;  // High byte of $0150

    // Put infinite loop at 0x150 (target of JP)
    rom[0x150] = 0x18;  // JR -2 (infinite loop)
    rom[0x151] = 0xFE;

    printf("ROM Configuration:\n");
    printf("  0x0100: JP $0150 (0xC3 0x50 0x01)\n");
    printf("  0x0150: JR -2 (infinite loop)\n\n");

    // Verify ROM bytes
    printf("ROM bytes at 0x100-0x105:\n  ");
    for (int i = 0; i < 6; i++) {
        printf("%02X ", rom[0x100 + i]);
    }
    printf("\n\n");

    printf("ROM bytes at 0x150-0x153:\n  ");
    for (int i = 0; i < 4; i++) {
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
    int loop_at_0x100 = 0;
    int loop_at_0x150 = 0;
    bool reached_0x150 = false;

    for (int cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot ROM completed at cycle %d, PC=$%04X\n\n", cycle, pc);
            printf("--- Cart ROM Execution Trace ---\n");
        }

        // Track cart ROM execution
        if (boot_completed && pc != last_pc) {
            cart_pc_changes++;

            // Print first 100 PC changes
            if (cart_pc_changes <= 100) {
                printf("  Cart PC[%3d]: $%04X", cart_pc_changes, pc);

                // Show what CPU should be executing at this address
                if (pc >= 0x100 && pc < 0x200) {
                    printf(" (ROM[$%04X] = 0x%02X)", pc, rom[pc]);
                }
                printf("\n");
            }

            // Detect looping at 0x100-0x103
            if (pc >= 0x100 && pc <= 0x103) {
                loop_at_0x100++;
                if (loop_at_0x100 == 20) {
                    printf("\n  ❌ ERROR: PC stuck looping at 0x0100-0x0103!\n");
                    printf("     JP instruction is NOT executing!\n");
                    printf("     This is a CRITICAL BUG with SDRAM latency\n\n");

                    printf("Expected execution:\n");
                    printf("  0x0100: Fetch opcode 0xC3 (JP)\n");
                    printf("  0x0101: Fetch low byte 0x50\n");
                    printf("  0x0102: Fetch high byte 0x01\n");
                    printf("  → JP to $0150\n\n");

                    printf("Actual execution:\n");
                    printf("  PC cycles: 0x0100 → 0x0101 → 0x0102 → 0x0103 → 0x0100 (repeating)\n");
                    printf("  JP instruction never executes!\n\n");

                    break;
                }
            }

            // Detect reaching 0x150 (target of JP)
            if (pc == 0x150 && !reached_0x150) {
                reached_0x150 = true;
                printf("\n  ✅ SUCCESS: Reached $0150 (JP executed correctly!)\n\n");
            }

            // Detect looping at 0x150
            if (pc == 0x150) {
                loop_at_0x150++;
                if (loop_at_0x150 == 5) {
                    printf("  ✅ Looping at $0150 (as expected)\n\n");
                    break;
                }
            }

            last_pc = pc;
        }
    }

    printf("\n=== Test Result ===\n");
    if (reached_0x150) {
        printf("✅ PASS: JP instruction executed correctly\n");
        printf("   PC reached target address $0150\n");
    } else {
        printf("❌ FAIL: JP instruction did NOT execute\n");
        printf("   PC stuck looping at 0x0100-0x0103\n");
        printf("   This indicates a BUG in CPU instruction fetch with SDRAM latency\n");
    }

    delete sdram;
    delete dut;
    return reached_0x150 ? 0 : 1;
}
