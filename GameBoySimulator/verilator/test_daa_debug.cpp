// Debug test for DAA instruction
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Test DAA with specific values
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // HALT everywhere

    // Entry point at $0100
    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // Test sequence at $0150:
    // We'll test DAA after ADD and SUB with specific values
    int bp = 0x150;

    // Test 1: DAA after ADD A, n - BCD addition
    // LD A, $15   ; A = 0x15 (BCD 15)
    // ADD A, $27  ; A = 0x3C, H=0, C=0
    // DAA         ; Should get 0x42 (15+27=42 in BCD)
    rom[bp++] = 0x3E; rom[bp++] = 0x15;  // LD A, $15
    rom[bp++] = 0xC6; rom[bp++] = 0x27;  // ADD A, $27
    rom[bp++] = 0x27;                     // DAA
    rom[bp++] = 0x47;                     // LD B, A (save result)

    // Test 2: DAA after ADD with low nibble overflow
    // LD A, $19   ; A = 0x19 (BCD 19)
    // ADD A, $01  ; A = 0x1A, sets H from low nibble
    // DAA         ; Should get 0x20 (19+1=20 in BCD)
    rom[bp++] = 0x3E; rom[bp++] = 0x19;  // LD A, $19
    rom[bp++] = 0xC6; rom[bp++] = 0x01;  // ADD A, $01
    rom[bp++] = 0x27;                     // DAA
    rom[bp++] = 0x4F;                     // LD C, A (save result)

    // Test 3: DAA after ADD with high nibble overflow
    // LD A, $99   ; A = 0x99 (BCD 99)
    // ADD A, $01  ; A = 0x9A
    // DAA         ; Should get 0x00 with C=1 (99+1=100 in BCD)
    rom[bp++] = 0x3E; rom[bp++] = 0x99;  // LD A, $99
    rom[bp++] = 0xC6; rom[bp++] = 0x01;  // ADD A, $01
    rom[bp++] = 0x27;                     // DAA
    rom[bp++] = 0x57;                     // LD D, A (save result)

    // Test 4: DAA after SUB
    // LD A, $20   ; A = 0x20 (BCD 20)
    // SUB A, $01  ; A = 0x1F, H=1 (borrow from high nibble)
    // DAA         ; Should get 0x19 (20-1=19 in BCD)
    rom[bp++] = 0x3E; rom[bp++] = 0x20;  // LD A, $20
    rom[bp++] = 0xD6; rom[bp++] = 0x01;  // SUB A, $01
    rom[bp++] = 0x27;                     // DAA
    rom[bp++] = 0x5F;                     // LD E, A (save result)

    // Test 5: Check A=0x9A -> DAA (no prior op, flags 0)
    // LD A, $B0   ; Force F to 0 (Z=1, others 0)
    // PUSH AF
    // POP AF      ; A=anything, F=B0
    // Actually let's use AND A to clear flags
    rom[bp++] = 0x3E; rom[bp++] = 0x9A;  // LD A, $9A
    rom[bp++] = 0xA7;                     // AND A (clears N, H, sets Z if A=0, preserves A)
    rom[bp++] = 0x27;                     // DAA
    rom[bp++] = 0x67;                     // LD H, A (save result)

    // Test 6: Check A=0xA0 with N=0 H=0 C=0
    rom[bp++] = 0x3E; rom[bp++] = 0xA0;  // LD A, $A0
    rom[bp++] = 0xA7;                     // AND A
    rom[bp++] = 0x27;                     // DAA
    rom[bp++] = 0x6F;                     // LD L, A (save result)

    rom[bp++] = 0x76;                     // HALT

    sdram->loadBinary(0, rom, sizeof(rom));

    // Boot ROM
    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;  // LD SP, $FFFE
    boot[i++] = 0x3E; boot[i++] = 0x91;                      // LD A, $91
    boot[i++] = 0xE0; boot[i++] = 0x40;                      // LDH ($40), A - Enable LCD
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;  // JP $0100

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

    printf("Testing DAA with detailed debug...\n\n");

    bool boot_done = false;
    bool in_test = false;
    uint8_t last_a = 0xFF;
    uint8_t last_f = 0xFF;
    uint8_t last_ir = 0xFF;

    for (int cycle = 0; cycle < 500000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t a = dut->dbg_cpu_acc;
        uint8_t f = dut->dbg_cpu_f;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;

        if (!boot_done && pc >= 0x150) {
            boot_done = true;
            printf("Boot complete at cycle %d, PC=%04X, entering test code...\n", cycle, pc);
        }

        if (boot_done && pc >= 0x150 && pc <= 0x190) {
            if (!in_test) {
                in_test = true;
                printf("\n=== DAA Test Sequence ===\n");
            }

            // Print every instruction transition
            if (ir != last_ir || a != last_a || f != last_f) {
                const char* insn = "";
                if (ir == 0x27) insn = "DAA";
                else if (ir == 0x3E) insn = "LD A,n";
                else if (ir == 0xC6) insn = "ADD A,n";
                else if (ir == 0xD6) insn = "SUB A,n";
                else if (ir == 0xA7) insn = "AND A";
                else if (ir == 0x47) insn = "LD B,A";
                else if (ir == 0x4F) insn = "LD C,A";
                else if (ir == 0x57) insn = "LD D,A";
                else if (ir == 0x5F) insn = "LD E,A";
                else if (ir == 0x67) insn = "LD H,A";
                else if (ir == 0x6F) insn = "LD L,A";
                else if (ir == 0x76) insn = "HALT";

                printf("cycle %6d: PC=%04X IR=%02X %-10s A=%02X F=%02X (Z=%d N=%d H=%d C=%d)\n",
                       cycle, pc, ir, insn, a, f,
                       (f >> 7) & 1, (f >> 6) & 1, (f >> 5) & 1, (f >> 4) & 1);
                last_ir = ir;
                last_a = a;
                last_f = f;
            }

            if (pc >= 0x180 && ir == 0x76) {
                printf("\n=== Test Results ===\n");
                uint8_t b = (dut->dbg_cpu_bc >> 8) & 0xFF;
                uint8_t c = dut->dbg_cpu_bc & 0xFF;
                uint8_t d = (dut->dbg_cpu_de >> 8) & 0xFF;
                uint8_t e = dut->dbg_cpu_de & 0xFF;
                uint8_t h = (dut->dbg_cpu_hl >> 8) & 0xFF;
                uint8_t l = dut->dbg_cpu_hl & 0xFF;

                printf("Test 1: 0x15 + 0x27 -> DAA = 0x%02X (expected 0x42)\n", b);
                printf("Test 2: 0x19 + 0x01 -> DAA = 0x%02X (expected 0x20)\n", c);
                printf("Test 3: 0x99 + 0x01 -> DAA = 0x%02X (expected 0x00 with C)\n", d);
                printf("Test 4: 0x20 - 0x01 -> DAA = 0x%02X (expected 0x19)\n", e);
                printf("Test 5: 0x9A AND A  -> DAA = 0x%02X (expected 0x00 with C)\n", h);
                printf("Test 6: 0xA0 AND A  -> DAA = 0x%02X (expected 0x00 with C)\n", l);
                break;
            }
        }

        if (cycle > 400000) {
            printf("Test taking too long! PC=%04X\n", pc);
            break;
        }
    }

    delete sdram;
    delete dut;
    return 0;
}
