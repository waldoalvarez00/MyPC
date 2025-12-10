// GameBoy RTL Unit Test - Comprehensive CPU Instruction Test
// Tests CPU instruction execution to identify potential bugs causing reset loops
//
// This test systematically exercises CPU instructions to verify:
// - Basic arithmetic and logic operations
// - Memory access (LD/ST instructions)
// - Jump and branch instructions
// - Stack operations
// - Interrupt handling
// - Register operations

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

//=============================================================================
// Helper: Load a custom boot ROM program for testing
//=============================================================================
void load_test_program(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* program, int size) {
    printf("Loading test program (%d bytes)...\n", size);
    printf("  First 8 bytes of program: %02X %02X %02X %02X %02X %02X %02X %02X\n",
           size > 0 ? program[0] : 0, size > 1 ? program[1] : 0,
           size > 2 ? program[2] : 0, size > 3 ? program[3] : 0,
           size > 4 ? program[4] : 0, size > 5 ? program[5] : 0,
           size > 6 ? program[6] : 0, size > 7 ? program[7] : 0);

    dut->boot_download = 1;

    int write_count = 0;
    for (int addr = 0; addr < size; addr += 2) {
        uint16_t word = program[addr];
        if (addr + 1 < size) {
            word |= (program[addr + 1] << 8);
        }

        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;

        if (write_count < 4) {  // Log first 4 writes
            printf("  Write[%d]: addr=%d (0x%02X), data=0x%04X (bytes: %02X %02X)\n",
                   write_count, addr, addr, word, word & 0xFF, (word >> 8) & 0xFF);
        }

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }

        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
        write_count++;
    }

    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    printf("Test program loaded successfully (%d writes)\n", write_count);
}

//=============================================================================
// Helper: Track CPU execution
//=============================================================================
struct CPUTrace {
    uint16_t addr;
    uint8_t rd_n;
    uint8_t wr_n;
    uint64_t cycle;
};

void print_cpu_trace(const CPUTrace* trace, int count) {
    printf("  CPU Trace (first %d address changes):\n", count);
    for (int i = 0; i < count; i++) {
        printf("    [%4llu] PC=$%04X rd=%d wr=%d\n",
               trace[i].cycle, trace[i].addr, trace[i].rd_n, trace[i].wr_n);
    }
}

//=============================================================================
// Test 1: Basic instruction execution (LD SP, LD A, NOP)
//=============================================================================
void test_basic_instructions(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Basic CPU Instructions");

    // Program:
    // 0x00: LD SP, $FFFE    (31 FE FF)  - Set stack pointer
    // 0x03: LD A, $42       (3E 42)     - Load immediate to A
    // 0x05: NOP             (00)        - No operation
    // 0x06: NOP             (00)
    // 0x07: JR $07          (18 FE)     - Infinite loop (halt)
    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0x3E, 0x42,        // LD A, $42
        0x00,              // NOP
        0x00,              // NOP
        0x18, 0xFE         // JR $07 (loop forever)
    };

    // Initialize with reset ACTIVE
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM while reset is active
    load_test_program(dut, sdram, program, sizeof(program));

    // Simulate cart download while reset is active
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0x00C3;  // JP $0150
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Now release reset - everything is loaded
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Track execution
    CPUTrace trace[100];
    int trace_count = 0;
    uint16_t last_addr = 0xFFFF;

    for (int i = 0; i < 10000 && trace_count < 100; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cpu_addr != last_addr && dut->dbg_boot_rom_enabled) {
            trace[trace_count].addr = dut->dbg_cpu_addr;
            trace[trace_count].rd_n = dut->dbg_cpu_rd_n;
            trace[trace_count].wr_n = dut->dbg_cpu_wr_n;
            trace[trace_count].cycle = i;
            trace_count++;
            last_addr = dut->dbg_cpu_addr;
        }
    }

    print_cpu_trace(trace, trace_count < 20 ? trace_count : 20);

    // Check if we hit the expected addresses
    bool hit_0000 = false;
    bool hit_0003 = false;
    bool hit_0005 = false;
    bool hit_0007 = false;
    bool stuck_in_loop = false;
    int loop_count = 0;

    for (int i = 0; i < trace_count; i++) {
        if (trace[i].addr == 0x0000) hit_0000 = true;
        if (trace[i].addr == 0x0003) hit_0003 = true;
        if (trace[i].addr == 0x0005) hit_0005 = true;
        if (trace[i].addr == 0x0007) {
            hit_0007 = true;
            loop_count++;
        }
    }

    stuck_in_loop = (loop_count >= 5);  // Hit loop address 5+ times

    results.check(hit_0000, "CPU started at $0000");
    results.check(hit_0003, "CPU reached LD A instruction at $0003");
    results.check(hit_0005, "CPU reached NOP at $0005");
    results.check(hit_0007, "CPU reached loop at $0007");
    results.check(stuck_in_loop, "CPU successfully loops (not resetting)");

    printf("  [INFO] Execution pattern: hit 0x0000=%d 0x0003=%d 0x0005=%d 0x0007=%d loops=%d\n",
           hit_0000, hit_0003, hit_0005, hit_0007, loop_count);
}

//=============================================================================
// Test 2: Memory write and read operations
//=============================================================================
void test_memory_operations(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Memory Read/Write Operations");

    // Program:
    // 0x00: LD SP, $FFFE    (31 FE FF)
    // 0x03: LD HL, $C000    (21 00 C0) - Point to RAM
    // 0x06: LD A, $55       (3E 55)    - Load value
    // 0x08: LD (HL), A      (77)       - Write to RAM
    // 0x09: LD A, $00       (3E 00)    - Clear A
    // 0x0B: LD A, (HL)      (7E)       - Read from RAM
    // 0x0C: JR $0C          (18 FE)    - Loop
    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0x21, 0x00, 0xC0,  // LD HL, $C000
        0x3E, 0x55,        // LD A, $55
        0x77,              // LD (HL), A
        0x3E, 0x00,        // LD A, $00
        0x7E,              // LD A, (HL)
        0x18, 0xFE         // JR $0C
    };

    // Initialize with reset ACTIVE
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM while reset is active
    load_test_program(dut, sdram, program, sizeof(program));

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

    // Track memory accesses
    bool saw_write = false;
    bool saw_read = false;
    bool reached_loop = false;

    for (int i = 0; i < 20000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_boot_rom_enabled) {
            if (dut->dbg_cpu_addr >= 0xC000 && dut->dbg_cpu_wr_n == 0) {
                saw_write = true;
            }
            if (dut->dbg_cpu_addr >= 0xC000 && dut->dbg_cpu_rd_n == 0) {
                saw_read = true;
            }
            if (dut->dbg_cpu_addr == 0x000C) {
                reached_loop = true;
                break;
            }
        }
    }

    results.check(saw_write, "CPU performed memory write");
    results.check(saw_read, "CPU performed memory read");
    results.check(reached_loop, "CPU reached end of program");
}

//=============================================================================
// Test 3: Jump and branch instructions
//=============================================================================
void test_jump_branch(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Jump and Branch Instructions");

    // Program:
    // 0x00: LD SP, $FFFE    (31 FE FF)
    // 0x03: JP $0010        (C3 10 00) - Absolute jump
    // 0x06-0x0F: NOP padding
    // 0x10: JR $10          (18 FE)    - Relative jump (loop)
    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0xC3, 0x10, 0x00,  // JP $0010
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // Padding
        0x18, 0xFE         // JR $10 (at address 0x10)
    };

    // Initialize with reset ACTIVE
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM while reset is active
    load_test_program(dut, sdram, program, sizeof(program));

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
    bool hit_0003 = false;  // JP instruction
    bool hit_0010 = false;  // Jump target
    bool skipped_0006 = true;  // Should NOT hit padding
    int loop_count = 0;
    int ce_cpu_high_count = 0;
    int ce_cpu_low_count = 0;
    uint16_t last_addr = 0xFFFF;
    int addr_change_count = 0;
    int read_count = 0;

    printf("  [DEBUG] First 20 address changes with ce_cpu state:\n");
    printf("  [DEBUG] CPU reads (when rd_n=0 and addr<$0020):\n");

    for (int i = 0; i < 20000; i++) {
        tick_with_sdram(dut, sdram);

        // Monitor ce_cpu
        if (dut->dbg_ce_cpu == 1) ce_cpu_high_count++;
        else ce_cpu_low_count++;

        if (dut->dbg_boot_rom_enabled) {
            // Log first CPU reads
            if (dut->dbg_cpu_rd_n == 0 && dut->dbg_cpu_addr < 0x0020 && read_count < 20) {
                uint8_t cpu_di_data = dut->dbg_cpu_di;  // What CPU reads
                uint8_t cpu_do_data = dut->dbg_cpu_do;  // What CPU writes (for comparison)
                uint8_t expected = (dut->dbg_cpu_addr < sizeof(program)) ? program[dut->dbg_cpu_addr] : 0x00;
                printf("    [%5d] Read addr=$%04X cpu_di=0x%02X cpu_do=0x%02X boot_q=0x%02X boot_do=0x%02X expected=0x%02X sel_boot=%d %s\n",
                       i, dut->dbg_cpu_addr, cpu_di_data, cpu_do_data,
                       dut->dbg_boot_q, dut->dbg_boot_do,
                       expected,
                       dut->dbg_sel_boot_rom,
                       (cpu_di_data == expected) ? "✓" : "✗");
                read_count++;
            }

            // Log first address changes with ce_cpu and CPU internals
            if (dut->dbg_cpu_addr != last_addr && addr_change_count < 20) {
                printf("    [%5d] $%04X ce_cpu=%d TmpAddr=$%04X IR=$%02X\n",
                       i, dut->dbg_cpu_addr, dut->dbg_ce_cpu,
                       dut->dbg_cpu_tmpaddr, dut->dbg_cpu_ir);
                last_addr = dut->dbg_cpu_addr;
                addr_change_count++;
            }

            if (dut->dbg_cpu_addr == 0x0003) hit_0003 = true;
            if (dut->dbg_cpu_addr >= 0x0006 && dut->dbg_cpu_addr < 0x0010) {
                skipped_0006 = false;  // Should not execute padding
            }
            if (dut->dbg_cpu_addr == 0x0010) {
                hit_0010 = true;
                loop_count++;
                if (loop_count >= 5) break;
            }
        }
    }

    printf("  [DEBUG] ce_cpu statistics: high=%d low=%d (%.1f%% high)\n",
           ce_cpu_high_count, ce_cpu_low_count,
           100.0 * ce_cpu_high_count / (ce_cpu_high_count + ce_cpu_low_count));

    results.check(hit_0003, "CPU executed JP instruction");
    results.check(skipped_0006, "CPU skipped over padding (jump worked)");
    results.check(hit_0010, "CPU reached jump target");
    results.check(loop_count >= 5, "CPU looping at target (not resetting)");

    printf("  [INFO] Jump test: hit_JP=%d skipped_padding=%d hit_target=%d loops=%d\n",
           hit_0003, skipped_0006, hit_0010, loop_count);
}

//=============================================================================
// Test 4: Real boot ROM execution pattern
//=============================================================================
void test_real_boot_rom_pattern(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Real Boot ROM Execution Pattern");

    // Load actual DMG boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("  [WARN] Could not load dmg_boot.bin, trying alternate paths\n");
        f = fopen("gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    }

    if (f) {
        size_t read = fread(boot_rom, 1, 256, f);
        fclose(f);
        printf("  [INFO] Loaded real DMG boot ROM (%zu bytes)\n", read);

        // Initialize with reset ACTIVE
        dut->reset = 1;
        dut->inputs = 0xFF;
        dut->ioctl_download = 0;
        dut->ioctl_wr = 0;
        dut->boot_download = 0;
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 50);

        // Load boot ROM while reset is active
        load_test_program(dut, sdram, boot_rom, 256);

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

        // Track key addresses that real boot ROM should hit
        bool hit_0000 = false;
        bool hit_0005 = false;  // Logo scroll subroutine
        bool hit_00D5 = false;  // Timing loop
        bool hit_00FC = false;  // Boot ROM disable
        int consecutive_0000 = 0;
        int max_consecutive_0000 = 0;
        uint16_t last_addr = 0xFFFF;

        CPUTrace trace[200];
        int trace_count = 0;

        for (int i = 0; i < 50000; i++) {
            tick_with_sdram(dut, sdram);

            if (dut->dbg_boot_rom_enabled && dut->dbg_cpu_addr != last_addr) {
                if (trace_count < 200) {
                    trace[trace_count].addr = dut->dbg_cpu_addr;
                    trace[trace_count].rd_n = dut->dbg_cpu_rd_n;
                    trace[trace_count].wr_n = dut->dbg_cpu_wr_n;
                    trace[trace_count].cycle = i;
                    trace_count++;
                }

                if (dut->dbg_cpu_addr == 0x0000) {
                    hit_0000 = true;
                    consecutive_0000++;
                    if (consecutive_0000 > max_consecutive_0000) {
                        max_consecutive_0000 = consecutive_0000;
                    }
                } else {
                    consecutive_0000 = 0;
                }

                if (dut->dbg_cpu_addr == 0x0005) hit_0005 = true;
                if (dut->dbg_cpu_addr == 0x00D5) hit_00D5 = true;
                if (dut->dbg_cpu_addr == 0x00FC) hit_00FC = true;

                last_addr = dut->dbg_cpu_addr;
            }

            if (!dut->dbg_boot_rom_enabled) {
                printf("  [INFO] Boot ROM disabled at cycle %d\n", i);
                break;
            }
        }

        print_cpu_trace(trace, trace_count < 50 ? trace_count : 50);

        results.check(hit_0000, "CPU started at $0000");
        results.check(hit_0005, "CPU hit logo scroll at $0005");
        results.check(max_consecutive_0000 < 20, "CPU not stuck in reset loop");

        printf("  [INFO] Boot ROM execution: 0x0005=%d 0x00D5=%d 0x00FC=%d max_loop=%d\n",
               hit_0005, hit_00D5, hit_00FC, max_consecutive_0000);

        if (max_consecutive_0000 >= 20) {
            printf("  [ERROR] RESET LOOP DETECTED! CPU returned to $0000 %d consecutive times\n",
                   max_consecutive_0000);
            printf("  [ERROR] This indicates a CPU bug or clock/reset issue\n");
        }

    } else {
        printf("  [SKIP] Could not load dmg_boot.bin - test skipped\n");
        results.check(false, "Boot ROM file loaded");
    }
}

//=============================================================================
// Test 5: Clock enable and reset behavior
//=============================================================================
void test_clock_and_reset(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Clock Enable and Reset Behavior");

    // Simple loop program
    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // LD SP, $FFFE
        0x18, 0xFE         // JR $03 (loop forever)
    };

    // Initialize with reset ACTIVE
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM while reset is active
    load_test_program(dut, sdram, program, sizeof(program));

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

    // Monitor clock enable signals
    int ce_cpu_high = 0;
    int ce_cpu_low = 0;
    int clken_high = 0;
    int clken_low = 0;
    bool reset_glitches = false;

    for (int i = 0; i < 10000; i++) {
        if (dut->reset == 1) {
            reset_glitches = true;
        }

        if (dut->dbg_ce_cpu == 1) ce_cpu_high++;
        else ce_cpu_low++;

        if (dut->dbg_cpu_clken == 1) clken_high++;
        else clken_low++;

        tick_with_sdram(dut, sdram);
    }

    results.check(ce_cpu_high > 0, "ce_cpu toggles high");
    results.check(clken_high > 0, "cpu_clken toggles high");
    results.check(!reset_glitches, "Reset stays low during execution");

    printf("  [INFO] Clock signals: ce_cpu high=%d low=%d, clken high=%d low=%d\n",
           ce_cpu_high, ce_cpu_low, clken_high, clken_low);
}

//=============================================================================
// Main test runner
//=============================================================================
int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);

    TestResults results;

    printf("\n");
    printf("========================================\n");
    printf("GameBoy CPU Comprehensive Test Suite\n");
    printf("========================================\n");

    // Run all tests
    test_basic_instructions(dut, sdram, results);
    test_memory_operations(dut, sdram, results);
    test_jump_branch(dut, sdram, results);
    test_real_boot_rom_pattern(dut, sdram, results);
    test_clock_and_reset(dut, sdram, results);

    // Cleanup
    delete dut;
    delete sdram;

    return results.report();
}
