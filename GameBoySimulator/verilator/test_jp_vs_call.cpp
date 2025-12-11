// Test to compare JP vs CALL instructions
// Both should jump to target address, but maybe one is broken?

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <cstdio>

void load_test_program(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* program, int size) {
    dut->boot_download = 1;
    for (int addr = 0; addr < size; addr += 2) {
        uint16_t word = program[addr];
        if (addr + 1 < size) word |= (program[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);
}

void run_test(const char* name, const uint8_t* program, int size, uint16_t expected_addr) {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("\n=== Test: %s ===\n", name);

    // Initialize with reset ACTIVE
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM while reset is active
    load_test_program(dut, sdram, program, size);

    // Simulate cart download while reset is active
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Now release reset
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Track execution
    uint16_t last_addr = 0xFFFF;
    bool hit_target = false;

    printf("First 10 address changes:\n");
    int count = 0;

    for (int i = 0; i < 10000 && count < 10; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cpu_addr != last_addr) {
            printf("  [%5d] $%04X", i, dut->dbg_cpu_addr);
            if (dut->dbg_cpu_addr == expected_addr) {
                printf(" ← TARGET!");
                hit_target = true;
            }
            printf("\n");
            last_addr = dut->dbg_cpu_addr;
            count++;
        }
    }

    printf("Result: %s\n", hit_target ? "PASS - Reached target" : "FAIL - Did not reach target");

    delete sdram;
    delete dut;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    // Test 1: JP $0010 (opcode C3)
    uint8_t jp_program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0xC3, 0x10, 0x00,  // JP $0010
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // Padding
        0x18, 0xFE         // JR $10 (loop)
    };
    run_test("JP $0010", jp_program, sizeof(jp_program), 0x0010);

    // Test 2: CALL $0010 (opcode CD)
    uint8_t call_program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0xCD, 0x10, 0x00,  // CALL $0010
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // Padding
        0x18, 0xFE         // JR $10 (loop)
    };
    run_test("CALL $0010", call_program, sizeof(call_program), 0x0010);

    // Test 3: JR (relative jump)
    uint8_t jr_program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0x18, 0x0A,        // JR +10 (to $000F)
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // Padding
        0x18, 0xFE         // JR $0F (loop)
    };
    run_test("JR +10", jr_program, sizeof(jr_program), 0x000F);

    return 0;
}
