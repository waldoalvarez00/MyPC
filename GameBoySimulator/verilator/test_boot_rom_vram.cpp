#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency
    
    printf("=== Boot ROM VRAM Write Diagnostic ===\n\n");
    
    // Load boot ROM
    uint8_t boot_rom[256];
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) {
        f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    }
    if (!f) {
        printf("ERROR: Could not load dmg_boot.bin\n");
        return 1;
    }
    fread(boot_rom, 1, 256, f);
    fclose(f);
    printf("✓ Loaded DMG boot ROM (256 bytes)\n");
    
    // Initialize with reset
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);

    // Load boot ROM via boot_download interface
    dut->boot_download = 1;
    for (int i = 0; i < 256; i += 2) {
        dut->boot_addr = i;  // Byte address (will be divided by 2 internally)
        dut->boot_data = boot_rom[i] | (boot_rom[i+1] << 8);
        dut->boot_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;
    
    // Simulate minimal cart header
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 1;
    dut->ioctl_addr = 0x0100 >> 1;  // Entry point
    dut->ioctl_dout = 0x00C3;  // JP $0150
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    
    run_cycles_with_sdram(dut, sdram, 100);

    // Release reset
    dut->reset = 0;

    printf("\n--- Monitoring Boot ROM Execution (from reset release) ---\n");
    printf("First 200 cycles (detailed):\n");

    int vram_write_count = 0;
    int boot_rom_reads = 0;
    bool saw_logo_copy = false;
    uint16_t last_pc = 0;
    uint16_t last_addr = 0;
    uint16_t first_vram_addr = 0;
    int pc_trace[100];
    int pc_trace_count = 0;
    bool printed_first_interrupt = false;

    for (int i = 0; i < 100000; i++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t addr = dut->dbg_cpu_addr;

        // Detailed logging for first 200 cycles
        if (i < 200 && (pc != last_pc || addr != last_addr)) {
            printf("  [%4d] PC=$%04X addr=$%04X boot_en=%d sel_boot=%d IE=$%02X IF=$%02X irq_n=%d rd=%d wr=%d DI=$%02X\n",
                   i, pc, addr, dut->dbg_boot_rom_enabled, dut->dbg_sel_boot_rom,
                   dut->dbg_ie_r, dut->dbg_if_r, dut->dbg_irq_n,
                   !dut->dbg_cpu_rd_n, !dut->dbg_cpu_wr_n, dut->dbg_cpu_di);
        }

        // Debug: Check for interrupt jump and boot ROM reading
        if (i >= 200 && i < 500 && pc != last_pc && pc < 0x0010) {
            printf("  [%4d] PC=$%04X addr=$%04X boot_en=%d sel_boot=%d IE=$%02X IF=$%02X irq_n=%d rd_n=%d DI=$%02X\n",
                   i, pc, addr, dut->dbg_boot_rom_enabled, dut->dbg_sel_boot_rom,
                   dut->dbg_ie_r, dut->dbg_if_r, dut->dbg_irq_n,
                   dut->dbg_cpu_rd_n, dut->dbg_cpu_di);
        }

        last_addr = addr;

        if (!printed_first_interrupt && pc == 0x0038 && last_pc != 0x0038) {
            printf("\n  [INTERRUPT] CPU jumped to $0038 at cycle %d (from PC=$%04X)\n", i, last_pc);
            printf("              This indicates an interrupt fired during boot\n\n");
            printed_first_interrupt = true;
        }

        // Track boot ROM execution
        if (dut->dbg_boot_rom_enabled) {
            if (pc != last_pc && pc < 0x0100) {
                boot_rom_reads++;

                // Record PC trace for first 100 unique addresses
                if (pc_trace_count < 100) {
                    pc_trace[pc_trace_count++] = pc;
                }

                // Check for logo copy routine (around $0005-$0033)
                if (pc >= 0x0005 && pc <= 0x0033) {
                    saw_logo_copy = true;
                }
            }
        }

        // Monitor VRAM writes ($8000-$9FFF)
        if (dut->dbg_cpu_wr_n == 0 &&
            dut->dbg_cpu_addr >= 0x8000 &&
            dut->dbg_cpu_addr < 0xA000) {

            if (vram_write_count == 0) {
                first_vram_addr = dut->dbg_cpu_addr;
                printf("  First VRAM write at cycle %d: [$%04X] = $%02X\n",
                       i, dut->dbg_cpu_addr, dut->dbg_cpu_do);
            }
            vram_write_count++;

            if (vram_write_count <= 10) {
                printf("  VRAM[%04X] = $%02X (write #%d)\n",
                       dut->dbg_cpu_addr, dut->dbg_cpu_do, vram_write_count);
            }
        }

        // Check if boot ROM disabled
        if (!dut->dbg_boot_rom_enabled && i > 1000) {
            printf("\n✓ Boot ROM disabled at cycle %d\n", i);
            break;
        }

        last_pc = pc;
    }
    
    printf("\n--- Results ---\n");
    printf("Boot ROM reads: %d\n", boot_rom_reads);
    printf("VRAM writes: %d\n", vram_write_count);
    printf("Logo copy routine: %s\n", saw_logo_copy ? "EXECUTED" : "NOT SEEN");
    printf("First VRAM addr: $%04X\n", first_vram_addr);

    printf("\n--- PC Trace (first %d unique addresses) ---\n", pc_trace_count);
    for (int i = 0; i < pc_trace_count && i < 20; i++) {
        printf("  [%2d] PC=$%04X\n", i, pc_trace[i]);
    }
    if (pc_trace_count > 20) {
        printf("  ... (%d more addresses)\n", pc_trace_count - 20);
    }
    
    printf("\n--- Analysis ---\n");
    if (vram_write_count == 0) {
        printf("✗ No VRAM writes detected - boot ROM logo copy failed\n");
        printf("  Possible causes:\n");
        printf("  - Boot ROM not executing\n");
        printf("  - VRAM write enable not working\n");
        printf("  - cpu_wr_n_edge timing issue\n");
    } else if (vram_write_count < 100) {
        printf("⚠ Only %d VRAM writes (expected ~200+ for full logo)\n", vram_write_count);
        printf("  Boot ROM may have crashed or stopped early\n");
    } else {
        printf("✓ VRAM writes occurred (%d total)\n", vram_write_count);
        printf("  Boot ROM logo copy appears to be working\n");
    }

    if (!saw_logo_copy) {
        printf("✗ Logo copy routine at $0005-$0033 not executed\n");
    } else {
        printf("✓ Logo copy routine was executed\n");
    }
    
    delete sdram;
    delete dut;
    return 0;
}
