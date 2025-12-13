// GameBoy Doctor - Cart ROM Only (Skip Boot ROM)
//
// Uses minimal boot ROM to quickly reach cart ROM for doctor logging

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include "gb_doctor_logger.h"

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

    const char* rom_path = "cpu_instrs/individual/01-special.gb";
    const char* log_path = "logs/cart_only_doctor.log";
    int max_instructions = 5000;

    if (argc > 1) rom_path = argv[1];
    if (argc > 2) log_path = argv[2];
    if (argc > 3) max_instructions = atoi(argv[3]);

    printf("=== GameBoy Doctor - Cart ROM Only (Skip Boot) ===\n\n");
    printf("ROM: %s\n", rom_path);
    printf("Log: %s\n", log_path);
    printf("Max logged instructions: %d\n\n", max_instructions);

    // Load ROM
    std::vector<uint8_t> rom;
    if (!load_file(rom_path, rom)) {
        fprintf(stderr, "Failed to load ROM: %s\n", rom_path);
        return 1;
    }
    printf("Loaded ROM: %zu bytes\n", rom.size());

    // Create MINIMAL boot ROM - just JP 0x0100
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    boot[0x000] = 0xC3;  // JP 0x0100
    boot[0x001] = 0x00;
    boot[0x002] = 0x01;
    printf("Using minimal boot ROM (JP 0x0100)\n");

    // Setup
    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    printf("Loading cart ROM to SDRAM...\n");
    sdram->loadBinary(0, rom.data(), rom.size());

    // Hold reset during ROM load
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

    upload_boot_rom(dut, sdram, boot, sizeof(boot));
    init_cart_ready(dut, sdram);

    printf("Releasing reset...\n");
    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("Creating doctor logger...\n");
    GBDoctorLogger logger(log_path, false);
    logger.set_boot_rom(boot, sizeof(boot));
    logger.set_enabled(true);

    printf("Running simulation...\n\n");
    const int max_cycles = 10000000;
    int instruction_count = 0;
    uint16_t prev_pc = 0xFFFF;
    bool reached_cart = false;

    for (int cycle = 0; cycle < max_cycles; cycle++) {
        tick_with_sdram(dut, sdram);

        // Log instructions
        if (instruction_count < max_instructions) {
            logger.tick(dut, sdram);
        }

        uint16_t curr_pc = dut->dbg_cpu_pc;
        if (curr_pc != prev_pc && prev_pc != 0xFFFF) {
            instruction_count++;

            // Detect cart ROM entry
            if (!reached_cart && curr_pc >= 0x0100 && curr_pc < 0x0150) {
                printf("✓ Reached cart ROM at PC=0x%04X (instruction %d, cycle %d)\n",
                    curr_pc, instruction_count, cycle);
                reached_cart = true;
            }

            // Progress
            if (instruction_count % 50000 == 0) {
                printf("  %d instructions (PC=0x%04X)...\n", instruction_count, curr_pc);
            }
        }
        prev_pc = curr_pc;

        // Stop if we've logged enough
        if (instruction_count >= max_instructions + 1000) {
            printf("\n✓ Logged %d instructions, stopping\n", max_instructions);
            break;
        }

        // Timeout
        if (instruction_count > 500000) {
            printf("\nTimeout after %d instructions\n", instruction_count);
            break;
        }
    }

    logger.flush();

    printf("\n=== Results ===\n");
    printf("Total instructions: %d\n", instruction_count);
    printf("Instructions logged: %lu\n", (unsigned long)logger.get_instruction_count());
    printf("Final PC: 0x%04X\n", dut->dbg_cpu_pc);
    printf("Reached cart ROM: %s\n", reached_cart ? "YES" : "NO");

    printf("\nLog file: %s\n", log_path);
    printf("\nView cart ROM execution:\n");
    printf("  grep 'PC:01' %s | head -20\n", log_path);
    printf("  grep 'PC:C' %s | head -20\n", log_path);

    delete dut;
    delete sdram;

    return 0;
}
