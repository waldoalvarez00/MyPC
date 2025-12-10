// Test to debug ClkEn vs cen mismatch
// Checks if ClkEn inside tv80_core matches the cen input

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
    printf("ClkEn Debug Test\n");
    printf("Checking if ClkEn matches cen\n");
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
    for (int i = 0; i < 100; i++) {
        tick();
    }

    // Load ROM
    for (size_t addr = 0; addr < sizeof(simple_lcd_rom); addr += 2) {
        uint16_t word = simple_lcd_rom[addr];
        if (addr + 1 < sizeof(simple_lcd_rom)) {
            word |= (simple_lcd_rom[addr + 1] << 8);
        }
        sdram->write16(addr, word);
    }

    top->reset = 0;

    for (int i = 0; i < 100; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    for (int i = 0; i < 2000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

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

    // Reset CPU
    top->reset = 1;
    for (int i = 0; i < 100; i++) {
        tick();
    }
    top->reset = 0;

    printf("\nCLKEN DEBUG TRACE:\n");
    printf("Cycle | PC     | cen | cpu_clken | ClkEn | BusAck | Match? | Notes\n");
    printf("------|--------|-----|-----------|-------|--------|--------|------------------------\n");

    uint16_t last_pc = 0xFFFF;
    int mismatches = 0;

    for (int i = 0; i < 500; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();

        uint16_t pc = top->dbg_cpu_addr;

        // Get the actual cen input to tv80_core
        // Path: gameboy -> cpu (GBse) -> i_tv80_core
        uint8_t cen = top->dbg_cpu_clken;  // This is CLKEN input to GBse, which becomes cen to tv80_core

        // Get ClkEn inside tv80_core
        uint8_t ClkEn = root->top__DOT__gameboy__DOT__cpu__DOT__i_tv80_core__DOT__ClkEn;
        uint8_t BusAck = root->top__DOT__gameboy__DOT__cpu__DOT__i_tv80_core__DOT__BusAck;

        bool match = (ClkEn == cen) || (ClkEn == (cen && !BusAck));

        if (!match || (pc != last_pc) || (cen && i < 100)) {
            const char* match_str = match ? "✓" : "✗ MISMATCH";
            char note[200] = "";

            if (pc != last_pc) {
                snprintf(note, sizeof(note), "PC: 0x%04X → 0x%04X", last_pc, pc);
                if (!cen) {
                    strcat(note, " *** WITH cen=0! ***");
                }
            } else if (cen) {
                snprintf(note, sizeof(note), "cen pulse");
            }

            if (!match) {
                mismatches++;
                snprintf(note, sizeof(note), "ClkEn should be (cen && !BusAck) = (%d && !%d) = %d",
                        cen, BusAck, cen && !BusAck);
            }

            printf(" %4d | 0x%04X | %d   |     %d     |   %d   |   %d    | %-10s | %s\n",
                   i, pc, cen, cen, ClkEn, BusAck, match_str, note);

            last_pc = pc;
        }

        if (i > 100 && pc > 0x0010) {
            break;
        }
    }

    printf("\n=== SUMMARY ===\n");
    printf("ClkEn mismatches: %d\n", mismatches);

    if (mismatches > 0) {
        printf("\n*** ClkEn NOT derived correctly from cen! ***\n");
        printf("This is a bug in tv80_core.v combinational logic.\n");
    } else {
        printf("\n*** ClkEn derived correctly from cen ***\n");
        printf("The problem must be elsewhere.\n");
    }

    top->final();
    delete top;
    delete sdram;

    return mismatches > 0 ? 1 : 0;
}
