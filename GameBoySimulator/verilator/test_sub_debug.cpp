// Debug test for SUB A, n instruction
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Simple test: SUB A, 5 in a loop until carry
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // HALT everywhere

    // Entry point at $0100
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // Test sequence at $0150:
    // LD A, $10     ; A = 16
    // SUB A, 5      ; A = A - 5, sets flags
    // JR NC, -4     ; Loop back to SUB if no carry
    // LD B, A       ; Save result
    // HALT
    rom[0x150] = 0x3E; rom[0x151] = 0x10;  // LD A, $10
    rom[0x152] = 0xD6; rom[0x153] = 0x05;  // SUB A, 5
    rom[0x154] = 0x30; rom[0x155] = 0xFC;  // JR NC, -4 (back to $0152)
    rom[0x156] = 0x47;                      // LD B, A
    rom[0x157] = 0x76;                      // HALT

    sdram->loadBinary(0, rom, sizeof(rom));

    // Boot ROM - setup and jump to cartridge
    uint8_t boot[256];
    memset(boot, 0, 256);
    int bp = 0;
    boot[bp++] = 0x31; boot[bp++] = 0xFE; boot[bp++] = 0xFF;  // LD SP, $FFFE
    boot[bp++] = 0x3E; boot[bp++] = 0x91;                      // LD A, $91
    boot[bp++] = 0xE0; boot[bp++] = 0x40;                      // LDH ($40), A - Enable LCD
    boot[bp++] = 0xC3; boot[bp++] = 0x00; boot[bp++] = 0x01;  // JP $0100

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Upload boot ROM
    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = boot[addr] | ((uint16_t)boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);

    // Initialize cart
    dut->ioctl_addr = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);
    for (int w = 0; w < 5000 && !dut->dbg_cart_ready; w++) {
        tick_with_sdram(dut, sdram);
    }

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("Testing SUB A, n with detailed debug...\n\n");

    bool boot_done = false;
    bool in_test = false;
    uint8_t last_a = 0xFF;
    uint8_t last_f = 0xFF;

    for (int cycle = 0; cycle < 500000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t a = dut->dbg_cpu_acc;
        uint8_t f = dut->dbg_cpu_f;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;

        // Boot is done when PC reaches $0150
        if (!boot_done && pc >= 0x150) {
            boot_done = true;
            printf("Boot complete at cycle %d, PC=%04X, entering test code...\n", cycle, pc);
        }

        // Track test progress
        if (boot_done && pc >= 0x150 && pc <= 0x158) {
            if (!in_test) {
                in_test = true;
                printf("\nStarting test, A=%02X, F=%02X\n", a, f);
            }

            // Print every cycle during SUB execution (IR=D6) to see what's happening
            if (ir == 0xD6) {
                printf("cycle %6d: PC=%04X IR=%02X A=%02X F=%02X mcycle=%02X tstate=%02X DI=%02X\n",
                       cycle, pc, ir, a, f, mcycle, tstate, dut->dbg_cpu_di);
            }

            // Print when A or F changes
            if (a != last_a || f != last_f) {
                printf("CHANGE %6d: PC=%04X IR=%02X A=%02X->%02X F=%02X->%02X mcycle=%02X tstate=%02X\n",
                       cycle, pc, ir, last_a, a, last_f, f, mcycle, tstate);
                last_a = a;
                last_f = f;
            }

            // Check if test completed (reached HALT at $0157)
            if (pc == 0x157 && ir == 0x76) {
                printf("\nTest completed! Final A=%02X (expected: 0x01 or 0xFC after wrap)\n", a);
                printf("B=%02X (should have A value)\n", (dut->dbg_cpu_bc >> 8) & 0xFF);
                break;
            }
        }

        // Check for stuck condition
        if (cycle > 400000) {
            printf("Test taking too long! PC=%04X A=%02X F=%02X\n", pc, a, f);
            break;
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
