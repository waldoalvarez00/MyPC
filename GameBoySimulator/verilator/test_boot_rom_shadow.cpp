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

    printf("=== Boot ROM Shadowing Analysis ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Load Nintendo logo into cart ROM via ioctl_download
    printf("Loading Nintendo logo to cart ROM via ioctl...\n");
    const uint8_t nintendo_logo[] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E
    };

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;  // Cart ROM download

    for (int i = 0; i < sizeof(nintendo_logo); i += 2) {
        dut->ioctl_addr = (0x0104 + i) >> 1;
        dut->ioctl_dout = nintendo_logo[i] | (nintendo_logo[i+1] << 8);
        dut->ioctl_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->ioctl_wr = 0;
        tick_with_sdram(dut, sdram);
    }
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 10);

    printf("Nintendo logo loaded. Starting boot ROM execution...\n\n");

    // Run boot ROM until it tries to read cart ROM header
    printf("Monitoring cart ROM reads during boot...\n");
    printf("Cycle | Addr | boot_en | sel_boot | cart_rd | sdram_oe | Data | Note\n");
    printf("------|------|---------|----------|---------|----------|------|------\n");

    bool found_logo_read = false;
    for (int cycle = 0; cycle < 50000; cycle++) {
        uint16_t cpu_addr = dut->dbg_cpu_addr;
        bool boot_en = dut->dbg_boot_rom_enabled;
        bool sel_boot = dut->dbg_sel_boot_rom;
        bool cart_rd = dut->dbg_cart_rd;
        bool sdram_oe = dut->dbg_sdram_oe;
        uint8_t data = dut->dbg_cpu_di;

        // Monitor reads from cart ROM header area ($0100-$014F)
        if (cpu_addr >= 0x0100 && cpu_addr <= 0x014F && cart_rd) {
            const char* note = "";
            if (cpu_addr >= 0x0104 && cpu_addr <= 0x0133) {
                note = "← LOGO READ";
                found_logo_read = true;
            } else if (cpu_addr == 0x0134) {
                note = "← TITLE";
            }

            printf("%5d | %04X | %7d | %8d | %7d | %8d | %02X   | %s\n",
                   cycle, cpu_addr, boot_en, sel_boot, cart_rd, sdram_oe, data, note);

            // If we read zeros from logo area while boot ROM enabled, that's the problem
            if (cpu_addr >= 0x0104 && cpu_addr <= 0x0133) {
                if (boot_en && data == 0x00) {
                    printf("      ^^^ BUG: boot_rom_enabled=1 blocks cart ROM read!\n");
                }
                if (sel_boot) {
                    printf("      ^^^ BUG: sel_boot_rom=1 blocks cart ROM read!\n");
                }
            }
        }

        // Check for boot ROM disable write to $FF50
        if (cpu_addr == 0xFF50 && !boot_en) {
            printf("%5d | FF50 | %7d | %8d | %7d | %8d |      | Boot ROM DISABLED\n",
                   cycle, boot_en, sel_boot, cart_rd, sdram_oe);
        }

        tick_with_sdram(dut, sdram);

        // Stop after boot ROM is disabled and we've seen logo reads
        if (!boot_en && found_logo_read) {
            break;
        }
    }

    printf("\n--- Analysis ---\n");
    if (found_logo_read) {
        printf("✅ Found cart ROM logo reads during boot\n");
    } else {
        printf("❌ Never saw cart ROM logo reads!\n");
    }

    delete sdram;
    delete dut;
    return found_logo_read ? 0 : 1;
}
