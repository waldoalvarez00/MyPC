// Continuous trace from reset to find where PC jumps from 0x0000 to 0x0001

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "../sim/mister_sdram_model.h"
#include "simple_lcd_rom.h"

Vtop* top = nullptr;
MisterSDRAMModel* sdram = nullptr;
vluint64_t main_time = 0;
int clk = 0;

uint16_t sdram_rdata = 0;
bool sdram_compl = false;
bool sdram_config_done = false;

void processSDRAM() {
    sdram->processNativeSDRAM(
        top->sd_cs, top->sd_ras, top->sd_cas, top->sd_we,
        top->sd_ba, top->sd_addr, top->sd_data_out, top->sd_dqm,
        sdram_rdata, sdram_compl, sdram_config_done
    );
    top->sd_data_in = sdram_rdata;
}

void tick() {
    clk = !clk;
    top->clk_sys = clk;
    top->eval();
    if (clk) {
        processSDRAM();
        main_time++;
    }
}

int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("Reset to Execution Continuous Trace\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);
    top = new Vtop();
    sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->debug = false;

    auto* root = top->rootp;

    // Initialize
    top->reset = 1;
    top->ioctl_download = 0;
    top->ioctl_wr = 0;
    top->ioctl_addr = 0;
    top->ioctl_dout = 0;
    top->ioctl_index = 0;
    top->inputs = 0xFF;
    top->boot_download = 0;
    top->boot_wr = 0;
    top->boot_addr = 0;
    top->boot_data = 0;

    // Initial reset
    printf("Resetting...\n");
    for (int i = 0; i < 100; i++) {
        tick();
    }

    // Load ROM to SDRAM model
    printf("Loading ROM to SDRAM (%zu bytes)...\n", sizeof(simple_lcd_rom));
    for (size_t addr = 0; addr < sizeof(simple_lcd_rom); addr += 2) {
        uint16_t word = simple_lcd_rom[addr];
        if (addr + 1 < sizeof(simple_lcd_rom)) {
            word |= (simple_lcd_rom[addr + 1] << 8);
        }
        sdram->write16(addr, word);
    }

    // Release reset
    printf("Releasing reset...\n");
    top->reset = 0;

    // Disable boot ROM
    for (int i = 0; i < 100; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // SDRAM init
    for (int i = 0; i < 2000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // ioctl download
    printf("Running ioctl download...\n");
    top->ioctl_download = 1;
    top->ioctl_index = 0;

    for (size_t addr = 0; addr < sizeof(simple_lcd_rom); addr += 2) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

        uint16_t word = simple_lcd_rom[addr];
        if (addr + 1 < sizeof(simple_lcd_rom)) {
            word |= (simple_lcd_rom[addr + 1] << 8);
        }
        top->ioctl_dout = word;
        top->ioctl_addr = addr;
        top->ioctl_wr = 1;

        for (int i = 0; i < 32; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }
        top->ioctl_wr = 0;
        for (int i = 0; i < 32; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }
    }
    top->ioctl_download = 0;

    for (int i = 0; i < 1000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    printf("  cart_ready=%d\n\n", top->dbg_cart_ready);

    // Reset CPU
    printf("Resetting CPU...\n");
    top->reset = 1;
    for (int i = 0; i < 100; i++) {
        tick();
    }
    top->reset = 0;

    // CONTINUOUS TRACE from reset through first instruction execution
    printf("\nCONTINUOUS TRACE:\n");
    printf("Cycle | PC     | M1 | RD | ce | rom_do | Notes\n");
    printf("------|--------|----|----|----|---------|-----------------------------------------\n");

    uint16_t last_pc = 0xFFFF;
    uint8_t last_m1 = 0xFF;
    bool pc_advanced = false;

    for (int i = 0; i < 500; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        top->ioctl_download = 0;
        tick();

        uint16_t pc = top->dbg_cpu_addr;
        uint8_t rom_do = root->top__DOT__rom_do;
        uint8_t cpu_m1_n = root->top__DOT__gameboy__DOT__cpu_m1_n;
        uint8_t cpu_rd_n = root->top__DOT__gameboy__DOT__cpu_rd_n;
        uint8_t cpu_mreq_n = root->top__DOT__gameboy__DOT__cpu_mreq_n;
        uint8_t ce_cpu = top->dbg_ce_cpu;

        bool is_m1_fetch = (cpu_m1_n == 0) && (cpu_mreq_n == 0) && (cpu_rd_n == 0);

        // Show on PC change, M1 change, or ce_cpu pulse
        if (pc != last_pc || cpu_m1_n != last_m1 || (ce_cpu && i < 50)) {
            char note[200] = "";

            if (pc != last_pc) {
                snprintf(note, sizeof(note), "*** PC CHANGED: 0x%04X → 0x%04X ***",
                        last_pc, pc);
                if (pc == 0x0001 && last_pc == 0x0000 && !pc_advanced) {
                    snprintf(note, sizeof(note),
                            "*** PROBLEM: PC jumped 0x0000 → 0x0001 (M1=%d, RD=%d, ce=%d) ***",
                            !cpu_m1_n, !cpu_rd_n, ce_cpu);
                    pc_advanced = true;
                }
            } else if (is_m1_fetch) {
                snprintf(note, sizeof(note), "M1: Opcode fetch = 0x%02X", rom_do);
            }

            printf(" %4d | 0x%04X | %d  | %d  | %d  | 0x%02X   | %s (clk_div=%d)\n",
                   i, pc, !cpu_m1_n, !cpu_rd_n, ce_cpu, rom_do, note, root->top__DOT__clk_div);

            last_pc = pc;
            last_m1 = cpu_m1_n;
        }

        if (i > 100 && pc == 0x0150) {
            printf("\n*** SUCCESS: Reached 0x0150! ***\n");
            break;
        }
        if (i > 100 && pc > 0x0010) {
            printf("\n*** PC advanced past 0x0010 without jumping ***\n");
            break;
        }
    }

    // Cleanup
    top->final();
    delete top;
    delete sdram;

    return 0;
}
// Add ce_cpu monitoring version at EOF
