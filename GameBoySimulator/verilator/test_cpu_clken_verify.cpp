// Test to verify CPU respects cpu_clken (the ACTUAL signal to CPU)
// Previous test monitored ce_cpu (wrong signal - just an input to gb module)
// This test monitors cpu_clken (correct signal - after gb.v processing)

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
    printf("CPU CLKEN Verification Test\n");
    printf("Monitors ACTUAL cpu_clken signal to CPU\n");
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

    // CRITICAL TEST: Monitor BOTH ce_cpu and cpu_clken
    printf("\nCRITICAL TEST: Monitoring ce_cpu vs cpu_clken\n");
    printf("Cycle | PC     | M1 | ce_cpu | cpu_clken | clk_div | Notes\n");
    printf("------|--------|----|----- ---|-----------|---------|------------------------------------------\n");

    uint16_t last_pc = 0xFFFF;
    uint8_t last_m1 = 0xFF;
    bool pc_advanced_when_clken_0 = false;
    int cycles_with_clken_1 = 0;
    int cycles_with_pc_change = 0;

    for (int i = 0; i < 500; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        top->ioctl_download = 0;
        tick();

        uint16_t pc = top->dbg_cpu_addr;
        uint8_t rom_do = root->top__DOT__rom_do;
        uint8_t cpu_m1_n = root->top__DOT__gameboy__DOT__cpu_m1_n;
        uint8_t cpu_rd_n = root->top__DOT__gameboy__DOT__cpu_rd_n;
        uint8_t cpu_mreq_n = root->top__DOT__gameboy__DOT__cpu_mreq_n;

        // THESE ARE THE CRITICAL SIGNALS:
        uint8_t ce_cpu = top->dbg_ce_cpu;              // Input to gb module
        uint8_t cpu_clken = top->dbg_cpu_clken;        // Actual signal to CPU!
        uint8_t clk_div = root->top__DOT__clk_div;

        bool is_m1_fetch = (cpu_m1_n == 0) && (cpu_mreq_n == 0) && (cpu_rd_n == 0);

        if (cpu_clken) {
            cycles_with_clken_1++;
        }

        // Check for PC advancing when cpu_clken=0
        if (pc != last_pc) {
            cycles_with_pc_change++;
            if (!cpu_clken) {
                pc_advanced_when_clken_0 = true;
                printf(" %4d | 0x%04X | %d  |   %d    |     %d     |   %d     | *** PC CHANGED with cpu_clken=0! ***\n",
                       i, pc, !cpu_m1_n, ce_cpu, cpu_clken, clk_div);
            }
        }

        // Show on PC change, M1 change, or cpu_clken pulse
        if (pc != last_pc || cpu_m1_n != last_m1 || (cpu_clken && i < 100)) {
            char note[200] = "";

            if (pc != last_pc) {
                snprintf(note, sizeof(note), "PC: 0x%04X → 0x%04X", last_pc, pc);
            } else if (is_m1_fetch) {
                snprintf(note, sizeof(note), "M1: Opcode fetch = 0x%02X", rom_do);
            } else if (cpu_clken) {
                snprintf(note, sizeof(note), "cpu_clken pulse");
            }

            if (i < 200 || (pc != last_pc)) {  // Show first 200 cycles or any PC change
                printf(" %4d | 0x%04X | %d  |   %d    |     %d     |   %d     | %s\n",
                       i, pc, !cpu_m1_n, ce_cpu, cpu_clken, clk_div, note);
            }

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

    // Summary
    printf("\n=== VERIFICATION SUMMARY ===\n");
    printf("Cycles with cpu_clken=1: %d\n", cycles_with_clken_1);
    printf("Cycles with PC changes: %d\n", cycles_with_pc_change);

    if (pc_advanced_when_clken_0) {
        printf("\n*** CRITICAL BUG: PC advanced when cpu_clken=0! ***\n");
        printf("This means the CPU does NOT respect the cpu_clken signal.\n");
        printf("The bug is in the CPU core (tv80_core.v or tv80_gameboy.v wrapper).\n");
    } else {
        printf("\n*** CPU RESPECTS cpu_clken correctly! ***\n");
        printf("All PC changes occurred only when cpu_clken=1.\n");
        printf("The problem may be elsewhere (timing, data path, etc.).\n");
    }

    // Cleanup
    top->final();
    delete top;
    delete sdram;

    return pc_advanced_when_clken_0 ? 1 : 0;
}
