// GameBoy Doctor Logger - Memory and Boot ROM Debug
//
// Investigates two issues:
// 1. Why PCMEM shows all zeros
// 2. Why PC stays in 0x0900 range instead of reaching 0x0150

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

void dump_memory_region(MisterSDRAMModel* sdram, uint16_t start, uint16_t end) {
    printf("\nMemory dump 0x%04X-0x%04X:\n", start, end);
    for (uint16_t addr = start; addr <= end; addr += 16) {
        printf("%04X: ", addr);
        for (int i = 0; i < 16 && (addr + i) <= end; i++) {
            uint8_t byte = sdram->read_byte(addr + i);
            printf("%02X ", byte);
        }
        printf("\n");
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== Memory and Boot ROM Debug ===\n\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Reset
    reset_dut_with_sdram(dut, sdram);

    printf("Step 1: Load minimal boot ROM (JP 0x0150)\n");
    printf("=========================================\n");

    // Minimal boot ROM: Just jump to 0x0150
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0x00, sizeof(minimal_boot));
    minimal_boot[0x000] = 0xC3;  // JP 0x0150
    minimal_boot[0x001] = 0x50;
    minimal_boot[0x002] = 0x01;

    // Upload boot ROM via boot_download interface
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

    printf("Boot ROM uploaded. First 16 bytes should be: C3 50 01 00 00...\n");
    dump_memory_region(sdram, 0x0000, 0x000F);

    run_cycles_with_sdram(dut, sdram, 64);

    printf("\nStep 2: Load simple test ROM at 0x0150\n");
    printf("=======================================\n");

    // Simple test program
    uint8_t test_program[] = {
        0x00,               // 0150: NOP
        0x3E, 0x42,        // 0151: LD A, $42
        0x47,               // 0153: LD B, A
        0x04,               // 0154: INC B
        0x21, 0x00, 0xC0,  // 0155: LD HL, $C000
        0x70,               // 0158: LD [HL], B
        0x23,               // 0159: INC HL
        0x7E,               // 015A: LD A, [HL]
        0x3D,               // 015B: DEC A
        0x18, 0xFE,        // 015C: JR -2
    };

    for (int i = 0; i < sizeof(test_program); i++) {
        sdram->write8(0x0150 + i, test_program[i]);
    }

    printf("Test ROM uploaded at 0x0150. Should be: 00 3E 42 47 04...\n");
    dump_memory_region(sdram, 0x0150, 0x015F);

    // Also add standard header at 0x0100
    sdram->write8(0x0100, 0x00);  // NOP
    sdram->write8(0x0101, 0xC3);  // JP
    sdram->write8(0x0102, 0x50);  // 0x0150
    sdram->write8(0x0103, 0x01);  //

    // Nintendo logo
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

    printf("\nCartridge header at 0x0100:\n");
    dump_memory_region(sdram, 0x0100, 0x010F);

    // Signal cartridge download
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

    // Wait for cart ready
    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 10000, sdram);

    printf("\nStep 3: Run CPU and monitor execution\n");
    printf("======================================\n");
    printf("Watching for PC changes and checking memory at each PC...\n\n");
    printf("Cycle | PC   | PCMEM (4 bytes)       | PC Memory Contents\n");
    printf("------|------|-----------------------|------------------------------------------\n");

    uint16_t prev_pc = 0xFFFF;
    int instruction_count = 0;

    for (int cycle = 0; cycle < 10000 && instruction_count < 100; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t curr_pc = dut->dbg_cpu_pc;

        // When PC changes, log it and check memory
        if (curr_pc != prev_pc && prev_pc != 0xFFFF) {
            // Read PCMEM using the same logic as the logger
            uint8_t pcmem[4];
            for (int i = 0; i < 4; i++) {
                uint16_t addr = (curr_pc + i) & 0xFFFF;
                if (addr < 0x8000) {
                    // Cart ROM area
                    pcmem[i] = sdram->read_byte(addr);
                } else {
                    pcmem[i] = 0x00;
                }
            }

            printf("%5d | %04X | %02X %02X %02X %02X          | ",
                cycle, curr_pc, pcmem[0], pcmem[1], pcmem[2], pcmem[3]);

            // Also try direct SDRAM read to compare
            uint8_t direct[4];
            for (int i = 0; i < 4; i++) {
                direct[i] = sdram->read_byte(curr_pc + i);
            }
            printf("Direct: %02X %02X %02X %02X",
                direct[0], direct[1], direct[2], direct[3]);

            // Mark special addresses
            if (curr_pc == 0x0000) printf(" <- Boot ROM start");
            if (curr_pc == 0x0100) printf(" <- Cart entry");
            if (curr_pc == 0x0150) printf(" <- Test code start!");

            printf("\n");

            instruction_count++;

            // Stop if we reach test code or get stuck
            if (curr_pc == 0x0150) {
                printf("\n✓ SUCCESS: Reached test code at 0x0150!\n");
                break;
            }
            if (curr_pc > 0x0900 && curr_pc < 0x0A00) {
                if (instruction_count > 20) {
                    printf("\n⚠ WARNING: Stuck in 0x0900 range!\n");
                    break;
                }
            }
        }

        prev_pc = curr_pc;
    }

    printf("\n\nStep 4: Memory region analysis\n");
    printf("===============================\n");

    printf("\nChecking key memory regions in SDRAM:\n");

    printf("\n0x0000-0x000F (Boot ROM start):\n");
    dump_memory_region(sdram, 0x0000, 0x000F);

    printf("\n0x0100-0x010F (Cart header):\n");
    dump_memory_region(sdram, 0x0100, 0x010F);

    printf("\n0x0150-0x015F (Test code):\n");
    dump_memory_region(sdram, 0x0150, 0x015F);

    printf("\n0x0900-0x090F (Where PC seems to be):\n");
    dump_memory_region(sdram, 0x0900, 0x090F);

    printf("\n0x0960-0x096F (End of 0x0900 range):\n");
    dump_memory_region(sdram, 0x0960, 0x096F);

    printf("\n\nStep 5: Check boot ROM and cart ROM status\n");
    printf("===========================================\n");
    printf("Boot ROM enabled: %d\n", dut->dbg_boot_rom_enabled);
    printf("Cart ready: %d\n", dut->dbg_cart_ready);
    printf("Current PC: 0x%04X\n", dut->dbg_cpu_pc);

    printf("\n\nDiagnosis:\n");
    printf("==========\n");

    // Check if SDRAM has data where PC is executing
    uint16_t pc = dut->dbg_cpu_pc;
    uint8_t byte_at_pc = sdram->read_byte(pc);
    printf("1. SDRAM at current PC (0x%04X) contains: 0x%02X\n", pc, byte_at_pc);

    // Check if 0x0150 has our test code
    uint8_t byte_at_0150 = sdram->read_byte(0x0150);
    printf("2. SDRAM at 0x0150 contains: 0x%02X (expected 0x00 = NOP)\n", byte_at_0150);

    // Check if 0x0000 has our boot ROM
    uint8_t byte_at_0000 = sdram->read_byte(0x0000);
    printf("3. SDRAM at 0x0000 contains: 0x%02X (expected 0xC3 = JP)\n", byte_at_0000);

    printf("\nPossible issues:\n");
    if (byte_at_pc == 0x00) {
        printf("  - PC is executing from region with all zeros\n");
        printf("  - Boot ROM may not be mapped correctly to CPU\n");
    }
    if (byte_at_0150 != 0x00) {
        printf("  - Test code not loaded at 0x0150\n");
    }
    if (pc >= 0x0900 && pc < 0x0A00) {
        printf("  - PC in unexpected 0x0900 range\n");
        printf("  - This may be internal ROM or uninitialized memory region\n");
    }

    delete dut;
    delete sdram;

    return 0;
}
