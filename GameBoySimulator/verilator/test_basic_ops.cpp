// Basic operations test - with proper tracing
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;

    int bp = 0x150;

    // Simple test sequence with LD to registers to save results
    // Test: LD A,0x42 -> LD B,A -> LD A,0x15 -> ADD A,0x27 -> LD C,A -> DAA -> LD D,A -> HALT

    rom[bp++] = 0x3E; rom[bp++] = 0x42;  // LD A, 0x42
    rom[bp++] = 0x47;                     // LD B, A (B should be 0x42)
    rom[bp++] = 0x3E; rom[bp++] = 0x15;  // LD A, 0x15
    rom[bp++] = 0xC6; rom[bp++] = 0x27;  // ADD A, 0x27 (A should be 0x3C)
    rom[bp++] = 0x4F;                     // LD C, A (C should be 0x3C)
    rom[bp++] = 0x27;                     // DAA (A should be 0x42)
    rom[bp++] = 0x57;                     // LD D, A (D should be 0x42)
    rom[bp++] = 0x76;                     // HALT

    sdram->loadBinary(0, rom, sizeof(rom));

    // Boot ROM
    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;
    boot[i++] = 0x3E; boot[i++] = 0x91;
    boot[i++] = 0xE0; boot[i++] = 0x40;
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

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

    printf("Testing basic operations with tracing...\n\n");

    bool boot_done = false;
    uint8_t last_ir = 0xFF;
    uint8_t last_a = 0xFF;
    uint8_t last_f = 0xFF;

    for (int cycle = 0; cycle < 100000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t a = dut->dbg_cpu_acc;
        uint8_t f = dut->dbg_cpu_f;

        if (!boot_done && pc >= 0x150) {
            boot_done = true;
            printf("Boot complete at PC=0x%04X\n\n", pc);
        }

        if (boot_done && pc >= 0x150 && pc <= 0x170) {
            // Trace instruction changes
            if (ir != last_ir || a != last_a || f != last_f) {
                const char* insn = "";
                if (ir == 0x3E) insn = "LD A,n";
                else if (ir == 0x47) insn = "LD B,A";
                else if (ir == 0x4F) insn = "LD C,A";
                else if (ir == 0x57) insn = "LD D,A";
                else if (ir == 0xC6) insn = "ADD A,n";
                else if (ir == 0x27) insn = "DAA";
                else if (ir == 0x76) insn = "HALT";

                printf("PC=%04X IR=%02X %-10s A=%02X F=%02X (Z=%d N=%d H=%d C=%d)\n",
                       pc, ir, insn, a, f, (f>>7)&1, (f>>6)&1, (f>>5)&1, (f>>4)&1);
                last_ir = ir;
                last_a = a;
                last_f = f;
            }

            if (ir == 0x76) {
                // Wait a bit for HALT to complete
                run_cycles_with_sdram(dut, sdram, 100);

                uint8_t b = (dut->dbg_cpu_bc >> 8) & 0xFF;
                uint8_t c = dut->dbg_cpu_bc & 0xFF;
                uint8_t d = (dut->dbg_cpu_de >> 8) & 0xFF;

                printf("\n=== Final Results ===\n");
                printf("B = 0x%02X (expect 0x42 from LD B,A)\n", b);
                printf("C = 0x%02X (expect 0x3C from ADD result)\n", c);
                printf("D = 0x%02X (expect 0x42 from DAA result)\n", d);

                bool pass = (b == 0x42) && (c == 0x3C) && (d == 0x42);
                printf("\n%s\n", pass ? "ALL TESTS PASSED!" : "SOME TESTS FAILED");
                break;
            }
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
