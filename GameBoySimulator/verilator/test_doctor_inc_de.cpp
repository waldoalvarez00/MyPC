// GameBoy Doctor Logger Test - INC DE with Corrected Reset Handling
//
// Demonstrates:
// 1. Proper reset handling during ROM load (fixes PC issue)
// 2. Boot ROM memory copy in logger (fixes PCMEM issue)

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include "gb_doctor_logger.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== GameBoy Doctor Logger - INC DE Test ===\n\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Prepare ROM data
    uint8_t rom[32768];
    memset(rom, 0x00, sizeof(rom));

    // Cart header
    rom[0x0100] = 0xC3;  // JP 0x0150
    rom[0x0101] = 0x50;
    rom[0x0102] = 0x01;

    // Nintendo logo
    const uint8_t logo[48] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E,
    };
    memcpy(&rom[0x0104], logo, sizeof(logo));

    // Test program at 0x0150
    // LD DE,0104 ; INC DE ; LD A,(DE) ; HALT
    int p = 0x0150;
    rom[p++] = 0x11; rom[p++] = 0x04; rom[p++] = 0x01;  // LD DE,0104
    rom[p++] = 0x1A;                                     // LD A,(DE)
    rom[p++] = 0x13;                                     // INC DE
    rom[p++] = 0x1A;                                     // LD A,(DE)
    rom[p++] = 0x76;                                     // HALT

    // Load ROM to SDRAM BEFORE holding reset
    sdram->loadBinary(0, rom, sizeof(rom));

    // Prepare boot ROM
    uint8_t boot_rom[256];
    memset(boot_rom, 0x00, sizeof(boot_rom));
    boot_rom[0x000] = 0xC3;  // JP 0x0150
    boot_rom[0x001] = 0x50;
    boot_rom[0x002] = 0x01;

    // CRITICAL: Hold reset during boot ROM upload
    printf("Step 1: Holding CPU in reset\n");
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

    // Upload boot ROM (CPU in reset)
    printf("Step 2: Uploading boot ROM\n");
    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = boot_rom[addr] | ((uint16_t)boot_rom[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);

    // Initialize cart (CPU in reset)
    printf("Step 3: Initializing cart\n");
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

    // Release reset
    printf("Step 4: Releasing reset\n");
    run_cycles_with_sdram(dut, sdram, 200);
    dut->reset = 0;

    // Create logger with boot ROM support
    printf("Step 5: Creating logger\n");
    GBDoctorLogger logger("logs/inc_de_doctor.log", false);
    logger.set_boot_rom(boot_rom, 256);  // Provide boot ROM for PCMEM
    logger.set_enabled(true);

    // Run until HALT
    printf("Step 6: Running simulation\n");
    const int max_cycles = 200000;
    bool halted = false;
    int instruction_count = 0;
    uint16_t prev_pc = 0xFFFF;

    for (int i = 0; i < max_cycles; i++) {
        tick_with_sdram(dut, sdram);
        logger.tick(dut, sdram);

        uint16_t curr_pc = dut->dbg_cpu_pc;
        if (curr_pc != prev_pc && prev_pc != 0xFFFF) {
            instruction_count++;
        }
        prev_pc = curr_pc;

        if (dut->dbg_cpu_pc == 0x0157 && (uint8_t)dut->dbg_cpu_ir == 0x76) {
            halted = true;
            break;
        }
    }

    logger.flush();

    printf("\n=== Test Results ===\n");
    printf("Halted: %s\n", halted ? "YES" : "NO");
    printf("Final PC: 0x%04X (expected 0x0157)\n", dut->dbg_cpu_pc);
    printf("Final DE: 0x%04X (expected 0x0105)\n", dut->dbg_cpu_de);
    printf("Final A:  0x%02X (expected 0xED)\n", (uint8_t)dut->dbg_cpu_acc);
    printf("Instructions logged: %lu\n", (unsigned long)logger.get_instruction_count());
    printf("Instructions executed: %d\n", instruction_count);

    bool test_passed = halted &&
                       (dut->dbg_cpu_de == 0x0105) &&
                       ((uint8_t)dut->dbg_cpu_acc == 0xED);

    printf("\n%s\n", test_passed ? "✓ TEST PASSED" : "✗ TEST FAILED");

    printf("\nLog file: logs/inc_de_doctor.log\n");
    printf("\nTo view the log:\n");
    printf("  head -20 logs/inc_de_doctor.log\n");
    printf("\nPCMEM should now show actual instruction bytes, not zeros!\n");

    delete dut;
    delete sdram;

    return test_passed ? 0 : 1;
}
