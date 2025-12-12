#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    // MisterSDRAMModel ctor takes size in MB (not bytes).
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Verification 2: Cart ROM Reads ===\n\n");

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

    // Setup cart ROM with Nintendo logo
    uint8_t nintendo_logo[] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
    };

    printf("Loading Nintendo logo into cart ROM at $0104...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;

    for (int i = 0; i < 48; i += 2) {
        uint16_t addr = (0x0104 + i) >> 1;
        uint16_t data = nintendo_logo[i] | (nintendo_logo[i+1] << 8);
        dut->ioctl_addr = addr;
        dut->ioctl_dout = data;
        dut->ioctl_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->ioctl_wr = 0;
    }

    // Entry point
    dut->ioctl_addr = 0x0100 >> 1;
    dut->ioctl_dout = 0x00C3;
    dut->ioctl_wr = 1;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    dut->ioctl_download = 0;
    printf("✓ Nintendo logo loaded\n\n");

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Monitoring CPU reads from cart ROM ($0104-$0133)...\n\n");

    int cart_reads = 0;
    int vram_writes = 0;
    uint16_t last_read_addr = 0;
    uint8_t last_read_data = 0;

    for (int i = 0; i < 30000; i++) {
        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t wr_n = dut->dbg_cpu_wr_n;
        uint8_t wr_edge = dut->dbg_cpu_wr_n_edge;
        uint8_t data_in = dut->dbg_cpu_di;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Monitor reads from Nintendo logo area
        if (rd_n == 0 && addr >= 0x0104 && addr < 0x0134 && boot_enabled) {
            cart_reads++;
            last_read_addr = addr;
            last_read_data = data_in;

            if (cart_reads <= 10 || cart_reads > 90) {
                int logo_idx = addr - 0x0104;
                uint8_t expected = nintendo_logo[logo_idx];
                printf("  [%6d] PC=$%04X read cart[$%04X]: got=$%02X expected=$%02X %s\n",
                       i, pc, addr, data_in, expected,
                       data_in == expected ? "✓" : "✗ MISMATCH!");
            } else if (cart_reads == 11) {
                printf("  ... (skipping middle reads)\n");
            }
        }

        // Monitor writes to logo VRAM
        if (addr >= 0x8010 && addr < 0x8090 && wr_n == 0 && wr_edge == 0) {
            vram_writes++;
        }

        tick_with_sdram(dut, sdram);

        if (!dut->dbg_boot_rom_enabled) {
            printf("\n  Boot ROM disabled at cycle %d\n", i);
            break;
        }
    }

    printf("\n--- Results ---\n");
    printf("Cart ROM reads from $0104-$0133: %d\n", cart_reads);
    printf("VRAM writes to $8010-$808F: %d\n", vram_writes);
    printf("Expected: ~48 reads and ~96 writes\n");

    if (cart_reads < 10) {
        printf("\n❌ FAIL: Cart ROM not being read!\n");
        printf("   Possible causes:\n");
        printf("   - Boot ROM stays enabled during cart ROM reads\n");
        printf("   - Address decoding issue\n");
        printf("   - Boot ROM doesn't reach logo copy code\n");
        return 1;
    } else if (cart_reads < 40) {
        printf("\n❌ FAIL: Cart ROM reads stopped prematurely (%d/48)\n", cart_reads);
        printf("   Logo copy loop may be exiting early\n");
        return 1;
    } else {
        printf("\n✓ Cart ROM being read\n");
        if (vram_writes < 90) {
            printf("❌ But VRAM writes incomplete (%d/96)\n", vram_writes);
            return 1;
        } else {
            printf("✅ PASS: Logo copy working!\n");
            return 0;
        }
    }
}
