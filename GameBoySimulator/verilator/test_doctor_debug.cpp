// GameBoy Doctor Logger - M-Cycle Debug Test
//
// Instruments the CPU to understand M-cycle signal behavior
// and find the correct instruction boundary detection logic

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== GameBoy M-Cycle Debug Test ===\n\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Reset system
    reset_dut_with_sdram(dut, sdram);
    printf("System reset complete\n\n");

    // Upload a minimal boot ROM (just jumps to 0x0150)
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0x00, sizeof(minimal_boot));
    minimal_boot[0x000] = 0xC3;  // JP 0x0150
    minimal_boot[0x001] = 0x50;
    minimal_boot[0x002] = 0x01;

    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = minimal_boot[addr] | ((uint16_t)minimal_boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    printf("Minimal boot ROM uploaded (JP 0x0150)\n\n");

    // Create a simple test program at 0x0150 in SDRAM
    // Just a few NOPs and an infinite loop
    uint8_t test_program[] = {
        0x00,               // 0150: NOP
        0x00,               // 0151: NOP
        0x3E, 0x42,        // 0152: LD A, $42
        0x47,               // 0154: LD B, A
        0x04,               // 0155: INC B
        0x18, 0xFE,        // 0156: JR -2 (infinite loop)
    };
    for (int i = 0; i < sizeof(test_program); i++) {
        sdram->write8(0x0150 + i, test_program[i]);
    }
    printf("Test program loaded at 0x0150:\n");
    printf("  0150: NOP\n");
    printf("  0151: NOP\n");
    printf("  0152: LD A, $42\n");
    printf("  0154: LD B, A\n");
    printf("  0155: INC B\n");
    printf("  0156: JR -2 (infinite loop)\n");
    printf("\n");

    // Initialize cartridge (just needs valid header)
    const uint8_t logo[48] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E,
    };
    for (int i = 0; i < 48; i++) {
        sdram->write8(0x0104 + i, logo[i]);
    }

    // Pulse ioctl to signal cart ready
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

    bool ready = wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 10000, sdram);
    if (ready) {
        printf("Cart ready!\n\n");
    } else {
        printf("WARNING: Cart not ready\n\n");
    }

    printf("Starting M-cycle instrumentation...\n");
    printf("Columns: Cycle | PC   | IR | M-cycle | T-state | A  | F  | BC   | DE   | HL   | SP   | Event\n");
    printf("---------------------------------------------------------------------------------------------\n");

    uint16_t prev_pc = 0xFFFF;
    uint8_t prev_ir = 0xFF;
    uint8_t prev_mcycle = 0xFF;
    uint8_t prev_tstate = 0xFF;
    int instruction_count = 0;
    int same_pc_count = 0;

    const int MAX_CYCLES = 2000;

    for (int cycle = 0; cycle < MAX_CYCLES; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t curr_pc = dut->dbg_cpu_pc;
        uint8_t curr_ir = dut->dbg_cpu_ir;
        uint8_t curr_mcycle = dut->dbg_cpu_mcycle & 0x07;
        uint8_t curr_tstate = dut->dbg_cpu_tstate & 0x07;
        uint8_t curr_a = dut->dbg_cpu_acc & 0xFF;
        uint8_t curr_f = dut->dbg_cpu_f & 0xFF;
        uint16_t curr_bc = dut->dbg_cpu_bc;
        uint16_t curr_de = dut->dbg_cpu_de;
        uint16_t curr_hl = dut->dbg_cpu_hl;
        uint16_t curr_sp = dut->dbg_cpu_sp;

        // Detect events
        bool pc_changed = (curr_pc != prev_pc);
        bool ir_changed = (curr_ir != prev_ir);
        bool mcycle_changed = (curr_mcycle != prev_mcycle);
        bool tstate_changed = (curr_tstate != prev_tstate);

        // Only log if PC is in our test region or something interesting happens
        bool should_log = false;
        const char* event = "";

        if (curr_pc >= 0x0150 && curr_pc <= 0x0158) {
            should_log = true;
        }

        if (pc_changed) {
            should_log = true;
            event = "PC_CHANGE";
            instruction_count++;
        } else if (ir_changed) {
            should_log = true;
            event = "IR_CHANGE";
        } else if (mcycle_changed && curr_mcycle == 1) {
            should_log = true;
            event = "M1_START";
        } else if (mcycle_changed) {
            should_log = true;
            event = "M_CHANGE";
        }

        if (should_log) {
            printf("%5d | %04X | %02X | M=%d      | T=%d      | %02X | %02X | %04X | %04X | %04X | %04X | %s\n",
                cycle, curr_pc, curr_ir, curr_mcycle, curr_tstate,
                curr_a, curr_f, curr_bc, curr_de, curr_hl, curr_sp, event);
        }

        // Check for infinite loop (test completion)
        if (curr_pc == 0x0156 || curr_pc == 0x0158) {
            same_pc_count++;
            if (same_pc_count > 100) {
                printf("\nDetected infinite loop at PC=0x%04X after cycle %d\n", curr_pc, cycle);
                break;
            }
        } else {
            same_pc_count = 0;
        }

        prev_pc = curr_pc;
        prev_ir = curr_ir;
        prev_mcycle = curr_mcycle;
        prev_tstate = curr_tstate;
    }

    printf("\n=== Summary ===\n");
    printf("Instructions detected (PC changes): %d\n", instruction_count);
    printf("\nKey Observations:\n");
    printf("  - M-cycle values observed: Check M= column\n");
    printf("  - M1 cycle detection: Look for M=1 transitions\n");
    printf("  - T-state progression: Check T= column\n");
    printf("  - Instruction boundaries: Look for PC_CHANGE events\n");

    delete dut;
    delete sdram;

    return 0;
}
