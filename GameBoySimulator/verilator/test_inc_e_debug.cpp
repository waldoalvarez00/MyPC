// Simple test to debug INC E instruction
#include "Vtop.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "../sim/mister_sdram_model.h"
#include <cstdio>
#include <cstdlib>
#include <cstring>

// Clock the simulation
void tick(Vtop* dut, MisterSDRAMModel* sdram, VerilatedVcdC* tfp, uint64_t& time_ns) {
    dut->clk_sys = 0;
    dut->eval();
    sdram->eval(0, dut->SDRAM_CLK, dut->SDRAM_CKE,
                dut->SDRAM_A, dut->SDRAM_BA, dut->SDRAM_DQ,
                dut->SDRAM_DQML, dut->SDRAM_DQMH,
                dut->SDRAM_nCS, dut->SDRAM_nCAS, dut->SDRAM_nRAS, dut->SDRAM_nWE);
    dut->eval();
    if (tfp) tfp->dump(time_ns);
    time_ns += 5;

    dut->clk_sys = 1;
    dut->eval();
    sdram->eval(1, dut->SDRAM_CLK, dut->SDRAM_CKE,
                dut->SDRAM_A, dut->SDRAM_BA, dut->SDRAM_DQ,
                dut->SDRAM_DQML, dut->SDRAM_DQMH,
                dut->SDRAM_nCS, dut->SDRAM_nCAS, dut->SDRAM_nRAS, dut->SDRAM_nWE);
    dut->eval();
    if (tfp) tfp->dump(time_ns);
    time_ns += 5;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    Vtop* dut = new Vtop;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);
    tfp->open("inc_e_debug.vcd");

    MisterSDRAMModel sdram(128 * 1024 * 1024);

    // Simple test program at 0x0100:
    // 0100: NOP (00)
    // 0101: LD DE,$0000 (11 00 00)
    // 0104: INC E (1C)
    // 0105: HALT (76)
    uint8_t program[] = {0x00, 0x11, 0x00, 0x00, 0x1C, 0x76};
    sdram.load_rom(program, sizeof(program), 0x0100);

    // Put jump to 0x100 at entry point
    uint8_t entry[] = {0x00, 0xC3, 0x00, 0x01};  // NOP, JP $0100
    sdram.load_rom(entry, sizeof(entry), 0x0000);

    // Set cart header checksum
    uint8_t header[0x50] = {0};
    header[0x4D] = 0x00;  // Checksum
    sdram.load_rom(header, sizeof(header), 0x0100);

    // Re-write program over header
    sdram.load_rom(program, sizeof(program), 0x0100);

    uint64_t time_ns = 0;

    // Reset
    dut->reset = 1;
    for (int i = 0; i < 100; i++) tick(dut, &sdram, tfp, time_ns);
    dut->reset = 0;

    // Run until we reach PC=0x104 (INC E)
    int max_cycles = 100000;
    int cycle = 0;
    bool at_inc_e = false;

    while (cycle < max_cycles && !at_inc_e) {
        tick(dut, &sdram, tfp, time_ns);
        cycle++;

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;

        // When we reach PC=0x104, start detailed logging
        if (pc == 0x0104 && mcycle == 1 && tstate == 2) {
            printf("=== Found INC E at PC=0x104 ===\n");
            printf("Cycle %d: PC=%04X mcycle=%d tstate=%d\n", cycle, pc, mcycle, tstate);

            // Get register values
            uint16_t de = dut->dbg_cpu_de;
            printf("DE = %04X (D=%02X, E=%02X)\n", de, (de >> 8) & 0xFF, de & 0xFF);

            // Run a few more cycles to see the result
            for (int i = 0; i < 20; i++) {
                tick(dut, &sdram, tfp, time_ns);
                pc = dut->dbg_cpu_pc;
                mcycle = dut->dbg_cpu_mcycle;
                tstate = dut->dbg_cpu_tstate;
                de = dut->dbg_cpu_de;

                printf("  +%d: PC=%04X mcycle=%d tstate=%d DE=%04X\n",
                       i+1, pc, mcycle, tstate, de);
            }

            at_inc_e = true;
        }
    }

    if (!at_inc_e) {
        printf("Never reached INC E at PC=0x104\n");
        printf("Final PC=%04X\n", dut->dbg_cpu_pc);
    }

    tfp->close();
    delete tfp;
    delete dut;

    return 0;
}
