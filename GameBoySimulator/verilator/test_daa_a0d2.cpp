// Test DAA specifically for values that might produce A0 or D2
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

    // Test cases that might produce A0 or D2 as DAA output
    // Test via PUSH DE; POP AF to set exact A and F values

    // Test 1: A=0xA0, F=0x00 (N=0,H=0,C=0) - expect 0x00 with C=1
    rom[bp++] = 0x11; rom[bp++] = 0x00; rom[bp++] = 0xA0;  // LD DE, $A000
    rom[bp++] = 0xD5;                                       // PUSH DE
    rom[bp++] = 0xF1;                                       // POP AF
    rom[bp++] = 0x27;                                       // DAA
    rom[bp++] = 0xC5;                                       // PUSH BC (save result)
    rom[bp++] = 0x47;                                       // LD B, A

    // Test 2: A=0x40, F=0x10 (N=0,H=0,C=1) - expect 0xA0
    rom[bp++] = 0x11; rom[bp++] = 0x10; rom[bp++] = 0x40;  // LD DE, $4010
    rom[bp++] = 0xD5;
    rom[bp++] = 0xF1;
    rom[bp++] = 0x27;
    rom[bp++] = 0x4F;                                       // LD C, A

    // Test 3: A=0x72, F=0x10 (N=0,H=0,C=1) - expect 0xD2
    rom[bp++] = 0x11; rom[bp++] = 0x10; rom[bp++] = 0x72;  // LD DE, $7210
    rom[bp++] = 0xD5;
    rom[bp++] = 0xF1;
    rom[bp++] = 0x27;
    rom[bp++] = 0x57;                                       // LD D, A

    // Test 4: A=0xA0, F=0x40 (N=1,H=0,C=0) - expect 0xA0 unchanged
    rom[bp++] = 0x11; rom[bp++] = 0x40; rom[bp++] = 0xA0;  // LD DE, $A040
    rom[bp++] = 0xD5;
    rom[bp++] = 0xF1;
    rom[bp++] = 0x27;
    rom[bp++] = 0x5F;                                       // LD E, A

    // Test 5: A=0xD2, F=0x40 (N=1,H=0,C=0) - expect 0xD2 unchanged
    rom[bp++] = 0x11; rom[bp++] = 0x40; rom[bp++] = 0xD2;  // LD DE, $D240
    rom[bp++] = 0xD5;
    rom[bp++] = 0xF1;
    rom[bp++] = 0x27;
    rom[bp++] = 0x67;                                       // LD H, A

    // Test 6: A=0x3A, F=0x30 (N=0,H=1,C=1) - low nibble adjust + high nibble
    rom[bp++] = 0x11; rom[bp++] = 0x30; rom[bp++] = 0x3A;  // LD DE, $3A30
    rom[bp++] = 0xD5;
    rom[bp++] = 0xF1;
    rom[bp++] = 0x27;
    rom[bp++] = 0x6F;                                       // LD L, A

    rom[bp++] = 0x76;                                       // HALT

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

    printf("Testing DAA with specific flag combinations...\n\n");

    bool boot_done = false;
    uint8_t last_ir = 0xFF;
    uint8_t last_a = 0xFF;
    uint8_t last_f = 0xFF;

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t a = dut->dbg_cpu_acc;
        uint8_t f = dut->dbg_cpu_f;

        if (!boot_done && pc >= 0x150) {
            boot_done = true;
            printf("Boot complete at PC=0x%04X\n\n", pc);
        }

        if (boot_done && pc >= 0x150 && pc <= 0x1B0) {
            if (ir != last_ir || a != last_a || f != last_f) {
                const char* insn = "";
                if (ir == 0x11) insn = "LD DE,nn";
                else if (ir == 0xD5) insn = "PUSH DE";
                else if (ir == 0xF1) insn = "POP AF";
                else if (ir == 0x27) insn = "DAA";
                else if (ir == 0x47) insn = "LD B,A";
                else if (ir == 0x4F) insn = "LD C,A";
                else if (ir == 0x57) insn = "LD D,A";
                else if (ir == 0x5F) insn = "LD E,A";
                else if (ir == 0x67) insn = "LD H,A";
                else if (ir == 0x6F) insn = "LD L,A";
                else if (ir == 0xC5) insn = "PUSH BC";
                else if (ir == 0x76) insn = "HALT";

                printf("PC=%04X IR=%02X %-12s A=%02X F=%02X (Z=%d N=%d H=%d C=%d)\n",
                       pc, ir, insn, a, f, (f>>7)&1, (f>>6)&1, (f>>5)&1, (f>>4)&1);
                last_ir = ir;
                last_a = a;
                last_f = f;
            }

            if (ir == 0x76) {
                run_cycles_with_sdram(dut, sdram, 100);

                uint8_t b = (dut->dbg_cpu_bc >> 8) & 0xFF;
                uint8_t c = dut->dbg_cpu_bc & 0xFF;
                uint8_t d = (dut->dbg_cpu_de >> 8) & 0xFF;
                uint8_t e = dut->dbg_cpu_de & 0xFF;
                uint8_t h = (dut->dbg_cpu_hl >> 8) & 0xFF;
                uint8_t l = dut->dbg_cpu_hl & 0xFF;

                printf("\n=== DAA Test Results ===\n");
                printf("Test 1: A=0xA0, F=0x00 -> DAA = 0x%02X (expect 0x00, C=1)\n", b);
                printf("Test 2: A=0x40, F=0x10(C=1) -> DAA = 0x%02X (expect 0xA0, C=1)\n", c);
                printf("Test 3: A=0x72, F=0x10(C=1) -> DAA = 0x%02X (expect 0xD2, C=1)\n", d);
                printf("Test 4: A=0xA0, F=0x40(N=1) -> DAA = 0x%02X (expect 0xA0)\n", e);
                printf("Test 5: A=0xD2, F=0x40(N=1) -> DAA = 0x%02X (expect 0xD2)\n", h);
                printf("Test 6: A=0x3A, F=0x30(H=1,C=1) -> DAA = 0x%02X (expect 0xA0)\n", l);

                // 0x3A + 6 = 0x40, then + 0x60 = 0xA0

                break;
            }
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
