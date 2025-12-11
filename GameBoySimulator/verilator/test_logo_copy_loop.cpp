#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Logo Copy Loop Analysis ===\n\n");

    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) return 1;
    fread(boot_rom, 1, 256, f);
    fclose(f);

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM
    dut->boot_download = 1;
    for (int i = 0; i < 256; i += 2) {
        dut->boot_addr = i;
        dut->boot_data = boot_rom[i] | (boot_rom[i+1] << 8);
        dut->boot_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;

    // Simulate cart
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Monitoring logo copy loop execution...\n");
    printf("Looking for PC in range $0006-$000B and VRAM writes to $8010+\n\n");

    uint16_t last_pc = 0xFFFF;
    uint16_t last_hl = 0;
    int loop_iterations = 0;
    int vram_writes = 0;
    bool in_loop = false;
    uint16_t first_vram_write = 0;
    uint16_t last_vram_write = 0;

    for (int i = 0; i < 30000; i++) {
        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;
        bool vram_wren = dut->dbg_vram_wren;

        // Track loop entry/exit
        if (pc >= 0x0006 && pc <= 0x000B) {
            if (!in_loop) {
                in_loop = true;
                printf("  [%6d] Entered logo copy loop at PC=$%04X, HL=$%04X\n", i, pc, hl);
            }

            // Count backward jumps as iterations
            if (pc == 0x0006 && last_pc == 0x000B) {
                loop_iterations++;
                if (loop_iterations <= 50) {
                    printf("  [%6d] Loop iteration #%d, HL=$%04X\n", i, loop_iterations, hl);
                }
            }
        } else if (in_loop) {
            printf("  [%6d] Exited logo copy loop at PC=$%04X, HL=$%04X\n", i, pc, hl);
            printf("            Total iterations: %d\n", loop_iterations);
            in_loop = false;
        }

        // Track VRAM writes
        if (addr >= 0x8000 && addr < 0xA000 && wr_n == 0 && wr_edge == 0) {
            vram_writes++;
            if (vram_writes == 1) first_vram_write = addr;
            last_vram_write = addr;

            if (vram_writes <= 20) {
                printf("  [%6d] VRAM write #%d to $%04X (PC=$%04X, HL=$%04X)\n",
                       i, vram_writes, addr, pc, hl);
            }
        }

        tick_with_sdram(dut, sdram);
        last_pc = pc;
        last_hl = hl;

        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  [%6d] Boot ROM disabled\n", i);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("Loop iterations: %d\n", loop_iterations);
    printf("VRAM writes: %d\n", vram_writes);
    if (vram_writes > 0) {
        printf("First VRAM write: $%04X\n", first_vram_write);
        printf("Last VRAM write: $%04X\n", last_vram_write);
        printf("Expected range: $8010-$808F (48 tiles × 2 bytes = 96 writes)\n");
    }

    if (loop_iterations < 48) {
        printf("\n✗ BUG: Loop only executed %d times, expected ~48!\n", loop_iterations);
        printf("  This explains why only %d VRAM writes occurred.\n", vram_writes);
    } else if (vram_writes < loop_iterations * 2) {
        printf("\n✗ BUG: Loop executed %d times but only %d VRAM writes!\n",
               loop_iterations, vram_writes);
        printf("  Each iteration should write 2 bytes (tile data).\n");
    }

    delete sdram;
    delete dut;
    return 0;
}
