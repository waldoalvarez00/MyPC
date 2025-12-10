// Test to check timing of cpu_clken vs PC changes
// Records values BEFORE and AFTER each clock edge

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

int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("CPU CLKEN Timing Analysis\n");
    printf("Checking signal timing around PC changes\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);
    top = new Vtop();
    sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
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
    top->clk_sys = 0;

    // Initial reset
    for (int i = 0; i < 100; i++) {
        clk = !clk;
        top->clk_sys = clk;
        top->eval();
        if (clk) {
            processSDRAM();
            main_time++;
        }
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
        clk = !clk;
        top->clk_sys = clk;
        top->eval();
        if (clk) {
            processSDRAM();
            main_time++;
        }
    }

    // SDRAM init
    for (int i = 0; i < 2000; i++) {
        clk = !clk;
        top->clk_sys = clk;
        top->eval();
        if (clk) {
            processSDRAM();
            main_time++;
        }
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
            clk = !clk;
            top->clk_sys = clk;
            top->eval();
            if (clk) {
                processSDRAM();
                main_time++;
            }
        }
        top->ioctl_wr = 0;
        for (int i = 0; i < 32; i++) {
            clk = !clk;
            top->clk_sys = clk;
            top->eval();
            if (clk) {
                processSDRAM();
                main_time++;
            }
        }
    }
    top->ioctl_download = 0;

    for (int i = 0; i < 1000; i++) {
        clk = !clk;
        top->clk_sys = clk;
        top->eval();
        if (clk) {
            processSDRAM();
            main_time++;
        }
    }

    // Reset CPU
    top->reset = 1;
    for (int i = 0; i < 100; i++) {
        clk = !clk;
        top->clk_sys = clk;
        top->eval();
        if (clk) {
            processSDRAM();
            main_time++;
        }
    }
    top->reset = 0;

    // DETAILED TIMING TEST
    printf("\nDetailed timing trace (showing posedge transitions):\n");
    printf("Cyc | Edge | PC     | cpu_clken | ce_cpu | Notes\n");
    printf("----|------|--------|-----------|--------|--------------------------------\n");

    uint16_t last_pc = 0xFFFF;
    int cycle = 0;
    bool found_bug = false;

    for (int i = 0; i < 1000 && cycle < 500; i++) {
        top->ioctl_download = 0;

        // Record state BEFORE posedge
        clk = !clk;
        top->clk_sys = clk;
        if (!clk) {  // negedge
            top->eval();
            continue;  // Skip negedge
        }

        // Now on posedge - record BEFORE state
        uint16_t pc_before = top->dbg_cpu_addr;
        uint8_t ce_cpu_before = top->dbg_ce_cpu;
        uint8_t cpu_clken_before = top->dbg_cpu_clken;

        // Evaluate posedge
        top->eval();
        processSDRAM();

        // Record AFTER state
        uint16_t pc_after = top->dbg_cpu_addr;
        uint8_t ce_cpu_after = top->dbg_ce_cpu;
        uint8_t cpu_clken_after = top->dbg_cpu_clken;

        // Check if PC changed during this posedge
        if (pc_after != pc_before && cycle > 10) {
            found_bug = true;
            printf("%3d | ↑    | 0x%04X | %d→%d       | %d→%d    | PC CHANGED: 0x%04X → 0x%04X%s\n",
                   cycle, pc_after,
                   cpu_clken_before, cpu_clken_after,
                   ce_cpu_before, ce_cpu_after,
                   pc_before, pc_after,
                   (cpu_clken_before == 0) ? " *** WITH cpu_clken=0!" : "");
        } else if ((cpu_clken_before || cpu_clken_after) && cycle < 200) {
            printf("%3d | ↑    | 0x%04X | %d→%d       | %d→%d    | cpu_clken pulse\n",
                   cycle, pc_after,
                   cpu_clken_before, cpu_clken_after,
                   ce_cpu_before, ce_cpu_after);
        }

        main_time++;
        cycle++;

        if (cycle > 100 && pc_after == 0x0150) {
            printf("\n*** Reached 0x0150! ***\n");
            break;
        }
        if (cycle > 100 && pc_after > 0x0010) {
            printf("\n*** PC advanced past 0x0010 ***\n");
            break;
        }
    }

    printf("\n=== RESULT ===\n");
    if (found_bug) {
        printf("BUG CONFIRMED: PC changed when cpu_clken=0\n");
        return 1;
    } else {
        printf("CPU respects cpu_clken correctly\n");
        return 0;
    }

    top->final();
    delete top;
    delete sdram;
}
