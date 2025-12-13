// GameBoy Doctor - Blargg CPU Test ROM Runner
//
// Runs Blargg's cpu_instrs test ROMs with doctor logging

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include "gb_doctor_logger.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

// Load a file into memory
static bool load_file(const char* path, std::vector<uint8_t>& out) {
    FILE* f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "Failed to open: %s\n", path);
        return false;
    }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz <= 0) {
        fclose(f);
        return false;
    }
    out.resize((size_t)sz);
    const size_t n = fread(out.data(), 1, (size_t)sz, f);
    fclose(f);
    return n == (size_t)sz;
}

// Upload boot ROM
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

// Initialize cart ready signal
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

    // Parse arguments
    const char* rom_path = "cpu_instrs/individual/01-special.gb";
    const char* boot_path = "dmg_boot.bin";
    const char* log_path = "logs/blargg_doctor.log";
    int max_instructions = 50000;  // Limit for doctor logging

    if (argc > 1) rom_path = argv[1];
    if (argc > 2) log_path = argv[2];
    if (argc > 3) max_instructions = atoi(argv[3]);

    printf("=== GameBoy Doctor - Blargg Test ROM Runner ===\n\n");
    printf("ROM: %s\n", rom_path);
    printf("Log: %s\n", log_path);
    printf("Max instructions: %d\n\n", max_instructions);

    // Load ROM
    std::vector<uint8_t> rom;
    if (!load_file(rom_path, rom)) {
        fprintf(stderr, "Failed to load ROM: %s\n", rom_path);
        return 1;
    }
    printf("Loaded ROM: %zu bytes\n", rom.size());

    // Load boot ROM (try both paths)
    std::vector<uint8_t> boot;
    if (!load_file(boot_path, boot) && !load_file("../dmg_boot.bin", boot)) {
        fprintf(stderr, "Warning: Boot ROM not found, using minimal boot ROM\n");
        // Create minimal boot ROM
        boot.resize(256);
        memset(boot.data(), 0x00, 256);
        boot[0x000] = 0xC3;  // JP 0x0100
        boot[0x001] = 0x00;
        boot[0x002] = 0x01;
    } else {
        printf("Loaded boot ROM: %zu bytes\n", boot.size());
    }

    // Setup simulation
    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Load cart ROM to SDRAM
    printf("Loading cart ROM to SDRAM...\n");
    sdram->loadBinary(0, rom.data(), rom.size());

    // Hold reset and upload boot ROM
    printf("Uploading boot ROM (CPU in reset)...\n");
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    upload_boot_rom(dut, sdram, boot.data(), boot.size());
    init_cart_ready(dut, sdram);

    // Release reset
    printf("Releasing reset...\n");
    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    // Create logger
    printf("Creating doctor logger...\n");
    GBDoctorLogger logger(log_path, false);
    logger.set_boot_rom(boot.data(), boot.size());
    logger.set_enabled(true);

    // Run simulation
    printf("Running simulation...\n");
    const int max_cycles = 50000000;  // 50M cycles max
    int instruction_count = 0;
    uint16_t prev_pc = 0xFFFF;
    bool halted = false;

    // Blargg tests write results to serial port
    uint8_t serial_buffer[256];
    int serial_len = 0;
    uint8_t prev_serial_control = 0;

    printf("\nSerial output:\n");

    for (int cycle = 0; cycle < max_cycles; cycle++) {
        tick_with_sdram(dut, sdram);

        // Log with doctor logger (up to max_instructions)
        if (instruction_count < max_instructions) {
            logger.tick(dut, sdram);
        }

        // Track instruction count
        uint16_t curr_pc = dut->dbg_cpu_pc;
        if (curr_pc != prev_pc && prev_pc != 0xFFFF) {
            instruction_count++;

            // Progress indicator
            if (instruction_count % 10000 == 0) {
                printf("  %d instructions executed...\n", instruction_count);
            }
        }
        prev_pc = curr_pc;

        // Check for HALT
        if (dut->dbg_cpu_pc == prev_pc && (uint8_t)dut->dbg_cpu_ir == 0x76) {
            if (!halted) {
                printf("\nCPU halted at PC=0x%04X after %d instructions\n", dut->dbg_cpu_pc, instruction_count);
                halted = true;
            }
        }

        // Capture serial output (Blargg tests use this for results)
        // Serial control register at 0xFF02, bit 7 = transfer start
        uint8_t serial_control = 0; // Would need to read from I/O port
        // For now, we'll just run until halt or timeout

        // Stop conditions
        if (halted && cycle > 100) {
            // Wait a bit after halt, then stop
            break;
        }

        // Timeout
        if (instruction_count > 1000000) {
            printf("\nTimeout after %d instructions\n", instruction_count);
            break;
        }
    }

    logger.flush();

    printf("\n=== Test Complete ===\n");
    printf("Total instructions: %d\n", instruction_count);
    printf("Instructions logged: %lu\n", (unsigned long)logger.get_instruction_count());
    printf("Final PC: 0x%04X\n", dut->dbg_cpu_pc);
    printf("Halted: %s\n", halted ? "YES" : "NO");
    printf("\nLog file: %s\n", log_path);

    printf("\nTo compare with reference:\n");
    printf("  python3 tools/compare_doctor_logs.py reference.log %s\n", log_path);

    printf("\nTo view the log:\n");
    printf("  head -50 %s\n", log_path);
    printf("  tail -50 %s\n", log_path);

    delete dut;
    delete sdram;

    return 0;
}
