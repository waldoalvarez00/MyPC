// GameBoy Doctor Logger Validation Test
//
// Loads a minimal test ROM (simple_test.gb) and validates that the
// gameboy-doctor logger correctly captures CPU state at instruction boundaries.

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include "gb_doctor_logger.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

static void upload_boot_rom(Vtop* dut, MisterSDRAMModel* sdram, const char* boot_path) {
    FILE* f = fopen(boot_path, "rb");
    if (!f) {
        fprintf(stderr, "ERROR: Failed to open boot ROM: %s\n", boot_path);
        return;
    }

    uint8_t boot[256];
    size_t read = fread(boot, 1, 256, f);
    fclose(f);

    if (read != 256) {
        fprintf(stderr, "WARNING: Boot ROM size is %zu bytes (expected 256)\n", read);
        // Pad with zeros
        memset(boot + read, 0x00, 256 - read);
    }

    dut->boot_download = 1;
    dut->boot_wr = 0;
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

    printf("Boot ROM uploaded: %s\n", boot_path);
}

static void upload_cart_rom(Vtop* dut, MisterSDRAMModel* sdram, const char* cart_path) {
    FILE* f = fopen(cart_path, "rb");
    if (!f) {
        fprintf(stderr, "ERROR: Failed to open cart ROM: %s\n", cart_path);
        return;
    }

    // Read entire ROM
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);

    uint8_t* rom = new uint8_t[size];
    fread(rom, 1, size, f);
    fclose(f);

    printf("Loading cart ROM: %s (%ld bytes)\n", cart_path, size);

    // Upload via ioctl interface
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);

    // Write ROM data
    for (long addr = 0; addr < size; addr++) {
        dut->ioctl_addr = addr;
        dut->ioctl_dout = rom[addr];
        dut->ioctl_wr = 1;
        run_cycles_with_sdram(dut, sdram, 2);
        dut->ioctl_wr = 0;
        run_cycles_with_sdram(dut, sdram, 2);

        if ((addr % 1024) == 0) {
            printf("\r  Uploading... %ld/%ld bytes", addr, size);
            fflush(stdout);
        }
    }
    printf("\r  Uploading... %ld/%ld bytes - DONE\n", size, size);

    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 256);

    delete[] rom;

    // Wait for cart_ready
    printf("Waiting for cart_ready...\n");
    bool ready = wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 10000, sdram);
    if (ready) {
        printf("Cart ready!\n");
    } else {
        fprintf(stderr, "WARNING: Cart not ready after 10000 cycles\n");
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== GameBoy Doctor Logger Validation Test ===\n\n");

    TestResults results;
    results.set_suite("Doctor Logger");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Initialize logger
    GBDoctorLogger logger("logs/simple_test_output.log", true);

    // Reset system
    reset_dut_with_sdram(dut, sdram);
    printf("System reset complete\n\n");

    // Upload a minimal boot ROM (just jumps to 0x0100)
    // For this test, we'll use a simple boot that doesn't initialize registers
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0x00, sizeof(minimal_boot));
    minimal_boot[0x000] = 0xC3;  // JP 0x0100
    minimal_boot[0x001] = 0x00;
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
    printf("Minimal boot ROM uploaded\n\n");

    // Upload test ROM
    upload_cart_rom(dut, sdram, "test_roms/simple_test.gb");

    // Enable logging from start
    logger.set_enabled(true);
    printf("\nLogger enabled - starting simulation\n\n");

    // Run simulation for enough cycles to execute the test program
    // ~15 instructions * ~50 cycles/instruction = 750 cycles
    // Add extra margin
    const int MAX_CYCLES = 5000;
    int cycles = 0;
    uint16_t prev_pc = 0xFFFF;
    int same_pc_count = 0;

    printf("Running simulation (max %d cycles)...\n", MAX_CYCLES);

    for (cycles = 0; cycles < MAX_CYCLES; cycles++) {
        // Tick logger first
        logger.tick(dut, sdram);

        // Run one cycle
        tick_with_sdram(dut, sdram);

        // Check for infinite loop (test completion)
        uint16_t curr_pc = dut->dbg_cpu_pc;
        if (curr_pc == prev_pc) {
            same_pc_count++;
            if (same_pc_count > 500) {
                printf("Detected infinite loop at PC=0x%04X after %d cycles\n", curr_pc, cycles);
                break;
            }
        } else {
            same_pc_count = 0;
            prev_pc = curr_pc;
        }

        if ((cycles % 1000) == 0 && cycles > 0) {
            printf("  Cycle %d, PC=0x%04X\n", cycles, curr_pc);
        }
    }

    logger.flush();

    printf("\nSimulation complete:\n");
    printf("  Total cycles: %d\n", cycles);
    printf("  Final PC: 0x%04X\n", dut->dbg_cpu_pc);
    printf("  Instructions logged: %lu\n", (unsigned long)logger.get_instruction_count());
    printf("  Log file: logs/simple_test_output.log\n");

    // Validate that we logged some instructions
    results.check(logger.get_instruction_count() > 0, "Logger captured instructions");
    if (logger.get_instruction_count() > 0) {
        printf("    Logged %lu instructions\n", (unsigned long)logger.get_instruction_count());
    }

    // Check final PC is at expected infinite loop location
    results.check(dut->dbg_cpu_pc == 0x015C || dut->dbg_cpu_pc == 0x015E,
                  "Program executed to completion");
    printf("    Final PC: 0x%04X\n", dut->dbg_cpu_pc);

    printf("\nNext step: Compare logs with reference\n");
    printf("  python3 tools/compare_doctor_logs.py logs/simple_test_reference.log logs/simple_test_output.log\n");

    delete dut;
    delete sdram;

    return results.report();
}
