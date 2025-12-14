// GameBoy Doctor - Compare Mode
//
// Uses boot ROM that initializes CPU to post-boot state for gameboy-doctor comparison:
// A:01 F:B0 B:00 C:13 D:00 E:D8 H:01 L:4D SP:FFFE PC:0100
// Also returns 0x90 for LY register reads (0xFF44)

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include "gb_doctor_logger.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <string>

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

// Create boot ROM that initializes CPU to post-boot state
// Post-boot state: A:01 F:B0 B:00 C:13 D:00 E:D8 H:01 L:4D SP:FFFE PC:0100
// Also enables LCD (LCDC = 0x91) so LY increments
static void create_postboot_rom(uint8_t* boot) {
    memset(boot, 0x00, 256);
    int i = 0;

    // 1. Set SP first (needed for PUSH/POP)
    boot[i++] = 0x31;  // LD SP, 0xFFFE
    boot[i++] = 0xFE;
    boot[i++] = 0xFF;

    // 2. Set B, C, D, E
    boot[i++] = 0x06;  // LD B, 0x00
    boot[i++] = 0x00;
    boot[i++] = 0x0E;  // LD C, 0x13
    boot[i++] = 0x13;
    boot[i++] = 0x16;  // LD D, 0x00
    boot[i++] = 0x00;
    boot[i++] = 0x1E;  // LD E, 0xD8
    boot[i++] = 0xD8;

    // 3. Enable LCD (LCDC = 0x91) - must do this before setting final A/F
    // 0x91 = LCD on, Window tile map 9800, Window off, BG/Window tile data 8000,
    //        BG tile map 9800, OBJ size 8x8, OBJ off, BG on
    boot[i++] = 0x3E;  // LD A, 0x91
    boot[i++] = 0x91;
    boot[i++] = 0xE0;  // LDH (0x40), A -> write to 0xFF40 (LCDC)
    boot[i++] = 0x40;

    // 4. Set H, L
    boot[i++] = 0x26;  // LD H, 0x01
    boot[i++] = 0x01;
    boot[i++] = 0x2E;  // LD L, 0x4D
    boot[i++] = 0x4D;

    // 5. Set A=0x01, F=0xB0 using PUSH/POP trick
    // Save DE (we'll use it as temp)
    boot[i++] = 0xD5;  // PUSH DE (D=00, E=D8)

    // Set D=0x01 (for A), E=0xB0 (for F)
    boot[i++] = 0x16;  // LD D, 0x01
    boot[i++] = 0x01;
    boot[i++] = 0x1E;  // LD E, 0xB0
    boot[i++] = 0xB0;
    boot[i++] = 0xD5;  // PUSH DE (0x01, 0xB0)
    boot[i++] = 0xF1;  // POP AF -> A=0x01, F=0xB0

    // Restore D, E
    boot[i++] = 0xD1;  // POP DE -> D=00, E=D8

    // 6. Jump to cart entry point
    boot[i++] = 0xC3;  // JP 0x0100
    boot[i++] = 0x00;
    boot[i++] = 0x01;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    const char* rom_path = "test_roms/cpu_instrs/individual/01-special.gb";
    const char* log_path = "logs/compare_doctor.log";
    const char* ref_path = "reference_logs/01-special.log";
    int max_instructions = 100000;

    if (argc > 1) rom_path = argv[1];
    if (argc > 2) log_path = argv[2];
    if (argc > 3) ref_path = argv[3];
    if (argc > 4) max_instructions = atoi(argv[4]);

    printf("=== GameBoy Doctor - Compare Mode ===\n\n");
    printf("ROM: %s\n", rom_path);
    printf("Log: %s\n", log_path);
    printf("Ref: %s\n", ref_path);
    printf("Max instructions: %d\n\n", max_instructions);

    // Load ROM
    std::vector<uint8_t> rom;
    if (!load_file(rom_path, rom)) {
        fprintf(stderr, "Failed to load ROM: %s\n", rom_path);
        return 1;
    }
    printf("Loaded ROM: %zu bytes\n", rom.size());

    // Create post-boot ROM
    uint8_t boot[256];
    create_postboot_rom(boot);
    printf("Using post-boot initialization ROM\n");

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
    logger.set_enabled(false);  // Start disabled, enable at PC=0x0100

    printf("Running simulation...\n\n");
    const int max_cycles = 100000000;  // 100M cycles
    int instruction_count = 0;
    int logged_count = 0;
    uint16_t prev_pc = 0xFFFF;
    bool started_logging = false;

    for (int cycle = 0; cycle < max_cycles; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t curr_pc = dut->dbg_cpu_pc;

        // Start logging when we reach PC=0x0100 (cart ROM entry)
        if (!started_logging && curr_pc == 0x0100) {
            printf("✓ Reached cart ROM at PC=0x0100 (cycle %d)\n", cycle);
            logger.set_enabled(true);
            // Log the initial state BEFORE the first instruction executes
            logger.log_initial_state(dut, sdram);
            started_logging = true;
        }

        // Log instructions (only after reaching cart ROM)
        if (started_logging && logged_count < max_instructions) {
            logger.tick(dut, sdram);
            if (logger.get_instruction_count() > (size_t)logged_count) {
                logged_count = logger.get_instruction_count();
            }
        }

        if (curr_pc != prev_pc && prev_pc != 0xFFFF) {
            instruction_count++;

            // Progress
            if (logged_count > 0 && logged_count % 10000 == 0 && logged_count != instruction_count) {
                printf("  %d instructions logged (PC=0x%04X)...\n", logged_count, curr_pc);
            }
        }
        prev_pc = curr_pc;

        // Stop if we've logged enough
        if (logged_count >= max_instructions) {
            printf("\n✓ Logged %d instructions, stopping\n", logged_count);
            break;
        }

        // Detect HALT
        if (started_logging && curr_pc == prev_pc) {
            // Check if halted (reading opcode 0x76)
            // For now, just timeout
        }

        // Timeout
        if (instruction_count > max_instructions * 2 + 1000) {
            printf("\nTimeout after %d total instructions\n", instruction_count);
            break;
        }
    }

    logger.flush();

    printf("\n=== Results ===\n");
    printf("Total instructions: %d\n", instruction_count);
    printf("Instructions logged: %d\n", logged_count);
    printf("Final PC: 0x%04X\n", dut->dbg_cpu_pc);

    printf("\nLog file: %s\n", log_path);

    // Quick comparison with reference
    printf("\n=== Quick Comparison ===\n");
    printf("Running: python3 gameboy-doctor/gameboy-doctor %s cpu_instrs 1\n\n", log_path);

    char cmd[1024];
    snprintf(cmd, sizeof(cmd), "cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator && python3 gameboy-doctor/gameboy-doctor %s cpu_instrs 1 2>&1 | head -50", log_path);
    system(cmd);

    delete dut;
    delete sdram;

    return 0;
}
