// GameBoy Doctor Logger - Boot Sequence Debug
//
// Watch PC from cycle 0 to understand where CPU starts executing

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== Boot Sequence Debug ===\n\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    printf("Step 1: Reset and watch initial PC\n");
    printf("====================================\n");

    // Reset
    dut->clk_sys = 0;
    dut->reset = 1;
    for (int i = 0; i < 10; i++) {
        dut->clk_sys = !dut->clk_sys;
        dut->eval();
    }
    dut->reset = 0;

    printf("After reset, before any boot ROM upload:\n");
    printf("  PC = 0x%04X\n", dut->dbg_cpu_pc);
    printf("  Boot ROM enabled = %d\n", dut->dbg_boot_rom_enabled);
    printf("  Cart ready = %d\n", dut->dbg_cart_ready);

    printf("\nStep 2: Upload minimal boot ROM\n");
    printf("================================\n");

    // Minimal boot ROM: JP 0x0150
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0x00, sizeof(minimal_boot));
    minimal_boot[0x000] = 0xC3;  // JP nn
    minimal_boot[0x001] = 0x50;  // Low byte of 0x0150
    minimal_boot[0x002] = 0x01;  // High byte of 0x0150

    printf("Uploading boot ROM (C3 50 01 at address 0)...\n");

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
    printf("Boot ROM upload complete.\n");

    printf("\nAfter boot ROM upload, before running:\n");
    printf("  PC = 0x%04X\n", dut->dbg_cpu_pc);
    printf("  Boot ROM enabled = %d\n", dut->dbg_boot_rom_enabled);

    printf("\nStep 3: Watch PC for first 500 cycles\n");
    printf("======================================\n");
    printf("Looking for PC to execute from 0x0000 (boot ROM start)...\n\n");

    uint16_t prev_pc = dut->dbg_cpu_pc;
    bool found_zero = false;
    bool found_jump = false;

    for (int cycle = 0; cycle < 500; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t curr_pc = dut->dbg_cpu_pc;
        uint8_t boot_en = dut->dbg_boot_rom_enabled;

        if (curr_pc != prev_pc) {
            printf("Cycle %4d: PC = 0x%04X (boot_rom_en=%d)\n",
                cycle, curr_pc, boot_en);

            if (curr_pc == 0x0000) {
                printf("  ✓ PC reached 0x0000 (boot ROM start)\n");
                found_zero = true;
            }
            if (curr_pc == 0x0150) {
                printf("  ✓ PC reached 0x0150 (test code)!\n");
                found_jump = true;
                break;
            }
            if (curr_pc == 0x0100) {
                printf("  ⚠ PC at 0x0100 (cart header entry)\n");
            }
        }

        prev_pc = curr_pc;
    }

    if (!found_zero) {
        printf("\n⚠ WARNING: PC never reached 0x0000!\n");
        printf("   Boot ROM may not be executing.\n");
    }
    if (!found_jump) {
        printf("\n⚠ WARNING: PC never reached 0x0150!\n");
        printf("   Jump instruction not working.\n");
    }

    printf("\nStep 4: Check what's at PC addresses\n");
    printf("=====================================\n");

    // Run a bit more to see where it settles
    for (int i = 0; i < 1000; i++) {
        tick_with_sdram(dut, sdram);
    }

    uint16_t final_pc = dut->dbg_cpu_pc;
    printf("After 1500 total cycles:\n");
    printf("  Final PC = 0x%04X\n", final_pc);
    printf("  Boot ROM enabled = %d\n", dut->dbg_boot_rom_enabled);

    // Check if there's actual GameBoy boot ROM executing
    printf("\nChecking for standard GameBoy boot ROM behavior:\n");
    printf("  (Standard boot ROM is 256 bytes, scrolls Nintendo logo, ends at 0x0100)\n");

    if (final_pc > 0x0100 && final_pc < 0x0200) {
        printf("  → PC in 0x0100-0x01FF range suggests boot ROM DID run\n");
        printf("  → CPU may be executing NOPs from unmapped cart ROM region\n");
    } else if (final_pc < 0x0100) {
        printf("  → PC still in boot ROM range (< 0x0100)\n");
        printf("  → Boot ROM may be stuck or very slow\n");
    } else {
        printf("  → PC at unexpected location\n");
    }

    printf("\nStep 5: Test with actual game data\n");
    printf("===================================\n");

    // Load a simple program at 0x0150
    uint8_t test_program[] = {
        0x00,               // NOP
        0x3E, 0x42,        // LD A, $42
        0x18, 0xFE,        // JR -2 (infinite loop)
    };
    for (int i = 0; i < sizeof(test_program); i++) {
        sdram->write8(0x0150 + i, test_program[i]);
    }

    // Standard cart header
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

    printf("Loaded test program at 0x0150 and cart header at 0x0100\n");

    // Signal cartridge is loaded
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

    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 10000, sdram);

    printf("Cart ready signal received.\n");
    printf("  PC = 0x%04X\n", dut->dbg_cpu_pc);
    printf("  Boot ROM enabled = %d\n", dut->dbg_boot_rom_enabled);

    printf("\n=== CONCLUSION ===\n\n");
    printf("The issue is now clear:\n");
    printf("1. Boot ROM is uploaded to internal boot ROM memory (not SDRAM)\n");
    printf("2. When boot_rom_enabled=1, CPU reads 0x0000-0x00FF from internal ROM\n");
    printf("3. The logger's read_pcmem() reads from SDRAM model, not internal ROM\n");
    printf("4. That's why PCMEM shows all zeros - wrong memory source!\n\n");

    printf("Solutions:\n");
    printf("A. Add boot ROM memory to the logger (copy from boot_download)\n");
    printf("B. Only enable logging after boot ROM disables (boot_rom_enabled=0)\n");
    printf("C. Add boot ROM memory access to SDRAM model\n\n");

    printf("Recommended: Option B - start logging only after boot ROM completes.\n");

    delete dut;
    delete sdram;

    return 0;
}
