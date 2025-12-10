//=============================================================================
// test_jump_debug.cpp - Debug jump instruction execution
//=============================================================================

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstdlib>

// Load boot ROM
void load_test_program(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* program, int size) {
    printf("Loading test program (%d bytes)...\n", size);
    dut->boot_download = 1;

    for (int addr = 0; addr < size; addr += 2) {
        uint16_t word = program[addr];
        if (addr + 1 < size) {
            word |= (program[addr + 1] << 8);
        }
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
        dut->boot_wr = 0;
        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 200);
    printf("Test program loaded successfully\n");
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

    // Program with JP instruction
    uint8_t program[] = {
        0x31, 0xFE, 0xFF,  // 0x00: LD SP, $FFFE
        0xC3, 0x10, 0x00,  // 0x03: JP $0010
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // 0x06-0x0F: Padding
        0x18, 0xFE         // 0x10: JR $10 (loop)
    };

    printf("=== Jump Instruction Debug Test ===\n");
    printf("Program:\n");
    printf("  $0000: 31 FE FF    LD SP, $FFFE\n");
    printf("  $0003: C3 10 00    JP $0010\n");
    printf("  $0006-$000F: NOP padding (should be skipped)\n");
    printf("  $0010: 18 FE       JR $10 (loop forever)\n");
    printf("\n");

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

    printf("Reset released, starting execution trace:\n");
    printf("Cycle | Addr  | RD | WR | ce_cpu | boot_en | Notes\n");
    printf("------|-------|----|----|---------|---------|-----------\n");

    uint16_t last_addr = 0xFFFF;
    int addr_change_count = 0;

    for (int i = 0; i < 50000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;

        // Print on address change
        if (addr != last_addr) {
            printf("%5d | $%04X | %d  | %d  |   %d     |    %d    | ",
                   i, addr,
                   dut->dbg_cpu_rd_n ? 0 : 1,
                   dut->dbg_cpu_wr_n ? 0 : 1,
                   dut->dbg_ce_cpu,
                   dut->dbg_boot_rom_enabled);

            // Annotate special addresses
            if (addr == 0x0000) printf("Reset vector");
            else if (addr == 0x0003) printf("JP $0010 instruction");
            else if (addr == 0x0004) printf("JP operand byte 1 ($10)");
            else if (addr == 0x0005) printf("JP operand byte 2 ($00)");
            else if (addr >= 0x0006 && addr <= 0x000F) printf("PADDING - Should NOT hit!");
            else if (addr == 0x0010) printf("TARGET - JR loop");
            else if (addr == 0x0100) printf("Cart entry point");

            printf("\n");

            last_addr = addr;
            addr_change_count++;

            // Stop after 100 address changes or reaching target loop
            if (addr_change_count > 100 || (addr == 0x0010 && addr_change_count > 10)) {
                printf("\n[Trace truncated after %d address changes]\n", addr_change_count);
                break;
            }
        }

        // Check if boot ROM got disabled
        if (!dut->dbg_boot_rom_enabled && addr_change_count > 0) {
            printf("\n*** Boot ROM DISABLED at cycle %d, addr=$%04X ***\n", i, addr);
            printf("This means CPU jumped to cart!\n");
            break;
        }

        tick_with_sdram(dut, sdram);
    }

    printf("\n=== Analysis ===\n");
    printf("Did CPU reach $0010 (jump target)? %s\n",
           (last_addr == 0x0010) ? "YES" : "NO");
    printf("Boot ROM still enabled? %s\n",
           dut->dbg_boot_rom_enabled ? "YES" : "NO");

    delete sdram;
    delete dut;
    return 0;
}
