// Simplified test to verify CPU respects cpu_clken
// Uses only top-level dbg_* signals (no internal hierarchy access)

#include <verilated.h>
#include "Vtop.h"
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
    printf("CPU CLKEN Test (ClkEn_wire Fix)\n");
    printf("Testing if PC advances when cpu_clken=0\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);
    top = new Vtop();
    sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;  // Realistic CAS latency
    sdram->debug = false;

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

    // Load ROM to SDRAM model
    for (size_t addr = 0; addr < sizeof(simple_lcd_rom); addr += 2) {
        uint16_t word = simple_lcd_rom[addr];
        if (addr + 1 < sizeof(simple_lcd_rom)) {
            word |= (simple_lcd_rom[addr + 1] << 8);
        }
        sdram->write16(addr, word);
    }

    // Release reset
    top->reset = 0;

    // Wait for init
    for (int i = 0; i < 100; i++) {
        tick();
    }

    // SDRAM init
    for (int i = 0; i < 2000; i++) {
        tick();
    }

    // ioctl download
    top->ioctl_download = 1;
    top->ioctl_index = 0;

    for (size_t addr = 0; addr < sizeof(simple_lcd_rom); addr += 2) {
        uint16_t word = simple_lcd_rom[addr];
        if (addr + 1 < sizeof(simple_lcd_rom)) {
            word |= (simple_lcd_rom[addr + 1] << 8);
        }
        top->ioctl_dout = word;
        top->ioctl_addr = addr;
        top->ioctl_wr = 1;

        for (int i = 0; i < 32; i++) {
            tick();
        }
        top->ioctl_wr = 0;
        for (int i = 0; i < 32; i++) {
            tick();
        }
    }
    top->ioctl_download = 0;

    for (int i = 0; i < 1000; i++) {
        tick();
    }

    // Reset CPU
    top->reset = 1;
    for (int i = 0; i < 100; i++) {
        tick();
    }
    top->reset = 0;

    // CRITICAL TEST: Monitor cpu_clken and PC
    printf("\nMonitoring PC changes with cpu_clken:\n");
    printf("Cycle | PC     | cpu_clken | ce_cpu | Notes\n");
    printf("------|--------|-----------|--------|--------------------------------\n");

    uint16_t last_pc = 0xFFFF;
    bool pc_advanced_when_clken_0 = false;
    int cycles_with_clken_1 = 0;
    int cycles_with_pc_change = 0;

    for (int i = 0; i < 500; i++) {
        top->ioctl_download = 0;
        tick();

        uint16_t pc = top->dbg_cpu_addr;
        uint8_t ce_cpu = top->dbg_ce_cpu;
        uint8_t cpu_clken = top->dbg_cpu_clken;

        if (cpu_clken) {
            cycles_with_clken_1++;
        }

        // Check for PC advancing when cpu_clken=0
        if (pc != last_pc) {
            cycles_with_pc_change++;
            if (!cpu_clken) {
                pc_advanced_when_clken_0 = true;
                printf(" %4d | 0x%04X |     %d     |   %d    | *** PC CHANGED with cpu_clken=0! ***\n",
                       i, pc, cpu_clken, ce_cpu);
            } else {
                // PC change with cpu_clken=1 is correct
                if (i < 200) {  // Show first 200 cycles
                    printf(" %4d | 0x%04X |     %d     |   %d    | PC: 0x%04X → 0x%04X (OK)\n",
                           i, pc, cpu_clken, ce_cpu, last_pc, pc);
                }
            }
            last_pc = pc;
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
    printf("\n=== TEST RESULTS ===\n");
    printf("Cycles with cpu_clken=1: %d\n", cycles_with_clken_1);
    printf("Cycles with PC changes: %d\n", cycles_with_pc_change);

    if (pc_advanced_when_clken_0) {
        printf("\n*** FAILURE: PC advanced when cpu_clken=0! ***\n");
        printf("The ClkEn_wire fix did NOT resolve the issue.\n");
        printf("The CPU still does not respect the cpu_clken signal.\n");
        return 1;
    } else {
        printf("\n*** SUCCESS: CPU respects cpu_clken correctly! ***\n");
        printf("All PC changes occurred only when cpu_clken=1.\n");
        printf("The ClkEn_wire fix has RESOLVED the bug!\n");
        return 0;
    }

    top->final();
    delete top;
    delete sdram;
}
