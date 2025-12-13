// Debug test for LD A,(HL+) instruction
// Traces internal signals to find why HL doesn't increment

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

static bool load_file(const char* path, std::vector<uint8_t>& out) {
    FILE* f = fopen(path, "rb");
    if (!f) return false;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz <= 0) { fclose(f); return false; }
    out.resize((size_t)sz);
    const size_t n = fread(out.data(), 1, (size_t)sz, f);
    fclose(f);
    return n == (size_t)sz;
}

static void upload_boot_rom(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* boot, size_t boot_size) {
    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < (int)boot_size; addr += 2) {
        uint16_t w = boot[addr];
        if (addr + 1 < (int)boot_size) w |= (uint16_t)boot[addr + 1] << 8;
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
}

static void init_cart_ready(Vtop* dut, MisterSDRAMModel* sdram) {
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);
    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 5000, sdram);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== LD A,(HL+) Debug Test ===\n\n");

    // Simple test ROM that executes LD A,(HL+) at a known location
    // ROM layout at 0x0100:
    //   0x0100: LD HL, 0x4000  (21 00 40)
    //   0x0103: LD A, (HL+)    (2A)
    //   0x0104: LD A, (HL+)    (2A)  - second one to see if L increments
    //   0x0105: JP 0x0105      (C3 05 01) - infinite loop
    std::vector<uint8_t> rom(32768, 0x00);
    rom[0x0100] = 0x21; rom[0x0101] = 0x00; rom[0x0102] = 0x40;  // LD HL, $4000
    rom[0x0103] = 0x2A;  // LD A, (HL+)
    rom[0x0104] = 0x2A;  // LD A, (HL+)
    rom[0x0105] = 0xC3; rom[0x0106] = 0x05; rom[0x0107] = 0x01;  // JP $0105

    // Put some data at 0x4000 (VRAM area)
    // For cart ROM, put data at address 0x4000 in the ROM
    // Actually, we need to be careful - GameBoy address 0x4000 is cart ROM bank 1
    // Let me use address 0x0150 instead which is in cart ROM bank 0

    // Revised: Use HL = 0x0150 to read from cart ROM area
    rom[0x0100] = 0x21; rom[0x0101] = 0x50; rom[0x0102] = 0x01;  // LD HL, $0150
    rom[0x0103] = 0x2A;  // LD A, (HL+)
    rom[0x0104] = 0x2A;  // LD A, (HL+)
    rom[0x0105] = 0xC3; rom[0x0106] = 0x05; rom[0x0107] = 0x01;  // JP $0105

    // Put test data at 0x0150
    rom[0x0150] = 0xAA;
    rom[0x0151] = 0xBB;
    rom[0x0152] = 0xCC;

    // Boot ROM: Initialize registers and jump to 0x0100
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;  // LD SP, $FFFE
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;  // JP $0100

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    printf("Loading cart ROM to SDRAM...\n");
    sdram->loadBinary(0, rom.data(), rom.size());

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    upload_boot_rom(dut, sdram, boot, sizeof(boot));
    init_cart_ready(dut, sdram);

    printf("Releasing reset...\n");
    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("Running simulation to track LD A,(HL+) execution...\n\n");

    // Wait for PC to reach 0x0100
    uint16_t prev_pc = 0;
    uint16_t prev_hl = 0;
    bool found_0100 = false;
    int logged_instructions = 0;

    printf("Cycle | PC     | MCycle | TState | HL     | A    | RegWE | RegAddr | Notes\n");
    printf("------|--------|--------|--------|--------|------|-------|---------|------\n");

    bool reached_loop = false;
    for (int cycle = 0; cycle < 100000 && !reached_loop; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t a = dut->dbg_cpu_acc;
        uint8_t ir = dut->dbg_cpu_ir;

        // Start tracking at PC=0x0100
        if (!found_0100 && pc == 0x0100) {
            found_0100 = true;
            printf("=== Reached PC=0x0100 ===\n");
        }

        // Check if we've reached the loop (JP executed once)
        if (found_0100 && pc == 0x0105 && ir == 0xC3) {
            reached_loop = true;
        }

        if (found_0100 && pc >= 0x0100 && pc <= 0x0110 && logged_instructions < 200) {
            // Log state changes
            bool changed = (pc != prev_pc) || (hl != prev_hl);

            // Always log when at important PCs or when HL changes
            if (pc == 0x0103 || pc == 0x0104 || changed) {
                const char* note = "";
                if (pc == 0x0100 && prev_pc != 0x0100) note = "LD HL,$0150";
                if (pc == 0x0103 && prev_pc != 0x0103) note = "LD A,(HL+) #1";
                if (pc == 0x0104 && prev_pc != 0x0104) note = "LD A,(HL+) #2";
                if (pc == 0x0105 && prev_pc != 0x0105) note = "JP $0105 (loop)";
                if (hl != prev_hl) {
                    static char buf[64];
                    snprintf(buf, sizeof(buf), "HL changed: %04X->%04X", prev_hl, hl);
                    note = buf;
                }

                uint8_t regweh = dut->dbg_cpu_regweh;
                uint8_t regwel = dut->dbg_cpu_regwel;
                uint8_t regaddra = dut->dbg_cpu_regaddra;
                printf("%5d | 0x%04X | %6d | %6d | 0x%04X | 0x%02X | %d%d    | %d       | %s (IR=0x%02X)\n",
                    cycle, pc, mcycle, tstate, hl, a, regweh, regwel, regaddra, note, ir);
                logged_instructions++;
            }
            prev_hl = hl;
        }

        prev_pc = pc;
    }

    // Final state
    printf("\n=== Final State ===\n");
    printf("PC: 0x%04X\n", dut->dbg_cpu_pc);
    printf("HL: 0x%04X\n", dut->dbg_cpu_hl);
    printf("A:  0x%02X\n", dut->dbg_cpu_acc);

    printf("\nExpected: After two LD A,(HL+) instructions with HL starting at 0x0150:\n");
    printf("  HL should be 0x0152\n");
    printf("  A should be 0xBB (second read)\n");

    if (dut->dbg_cpu_hl == 0x0152) {
        printf("\n*** PASS: HL incremented correctly! ***\n");
    } else {
        printf("\n*** FAIL: HL = 0x%04X (expected 0x0152) ***\n", dut->dbg_cpu_hl);
        if (dut->dbg_cpu_hl == 0x0150) {
            printf("    HL did not increment at all - BUG CONFIRMED\n");
        }
    }

    delete dut;
    delete sdram;

    return 0;
}
