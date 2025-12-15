// Debug test for INC/DEC flag handling
// Traces Save_ALU_r and F_Out_r at each T-state
#include <verilated.h>
#include "Vtop.h"
#include "Vtop_top.h"
#include "Vtop_gb.h"
#include "Vtop_GBse.h"
#include "Vtop_tv80_core__pi1.h"
#include "gb_test_common.h"
#include <cstdint>
#include <cstdio>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("=== INC/DEC Flag Debug Test ===\n\n");

    // Create DUT and SDRAM model
    Vtop* dut = new Vtop;
    MisterSDRAMModel sdram(8, INTERFACE_NATIVE_SDRAM);
    sdram.cas_latency = 2;
    sdram.debug = false;

    // Create a simple test ROM:
    // 0x0150: LD C,$10   ; 0E 10  - Load C with 0x10
    // 0x0152: DEC C      ; 0D     - Decrement C (should set N=1, H=1)
    // 0x0153: INC C      ; 0C     - Increment C (should set N=0, H=0)
    // 0x0154: HALT       ; 76
    std::vector<uint8_t> rom(32768, 0);

    // Minimal header for cartridge validation
    rom[0x0104] = 0xCE; // Part of Nintendo logo (just enough to pass checksum)

    // Entry point at 0x0150
    rom[0x0150] = 0x0E; // LD C,n
    rom[0x0151] = 0x10; // immediate: 0x10
    rom[0x0152] = 0x0D; // DEC C
    rom[0x0153] = 0x0C; // INC C
    rom[0x0154] = 0x76; // HALT

    // Jump from 0x0100 to 0x0150
    rom[0x0100] = 0xC3; // JP nn
    rom[0x0101] = 0x50; // low byte
    rom[0x0102] = 0x01; // high byte

    // Create minimal boot ROM that jumps to 0x0100
    std::vector<uint8_t> boot(256, 0);
    boot[0x00] = 0xC3;  // JP 0x0100
    boot[0x01] = 0x00;
    boot[0x02] = 0x01;

    // Load ROM to SDRAM
    sdram.loadBinary(0, rom.data(), rom.size());

    // Reset
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, &sdram, 200);
    dut->reset = 0;

    // Upload boot ROM
    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = boot[addr];
        if (addr + 1 < 256) w |= (uint16_t)boot[addr + 1] << 8;
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, &sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, &sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, &sdram, 64);

    // Initialize cart
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, &sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, &sdram, 64);
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, &sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, &sdram, 256);
    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 5000, &sdram);

    printf("Running simulation...\n");

    // Access the cpu core
    auto* top_module = dut->top;
    auto* gb_module = top_module->gameboy;
    auto* cpu_module = gb_module->cpu;
    auto* cpu_core = cpu_module->i_tv80_core;

    uint8_t prev_tstate = 0;
    uint16_t prev_pc = 0;
    bool logging = false;

    for (int i = 0; i < 200000; i++) {
        run_cycles_with_sdram(dut, &sdram, 1);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t f = dut->dbg_cpu_f;

        // Access internal CPU signals
        uint8_t save_alu_r = cpu_core->__PVT__Save_ALU_r;
        uint8_t alu_op_r = cpu_core->__PVT__ALU_Op_r;
        uint8_t f_out_r = cpu_core->__PVT__F_Out_r;
        uint8_t save_alu = cpu_core->__PVT__Save_ALU;
        uint8_t preserve_c = cpu_core->__PVT__PreserveC;
        uint8_t f_out = cpu_core->__PVT__F_Out;
        uint8_t bus_a = cpu_core->__PVT__BusA;
        uint8_t bus_b = cpu_core->__PVT__BusB;
        uint8_t alu_op = cpu_core->__PVT__ALU_Op;
        uint8_t tstates_val = cpu_core->__PVT__tstates;
        uint8_t t_res = cpu_core->__PVT__last_tstate;

        // Start logging at PC=0x0150
        if (pc == 0x0150 && !logging) {
            printf("\n=== Starting detailed logging at PC=0x0150 ===\n");
            logging = true;
        }

        // Only log when state changes
        if (logging && (tstate != prev_tstate || pc != prev_pc)) {
            prev_tstate = tstate;
            prev_pc = pc;

            // Decode tstate
            int t = 0;
            for (int b = 0; b < 7; b++) {
                if (tstate & (1 << b)) t = b + 1;
            }

            // Decode mcycle
            int m = 0;
            for (int b = 0; b < 7; b++) {
                if (mcycle & (1 << b)) m = b + 1;
            }

            printf("PC=%04X M%d T%d T_Res=%d IR=%02X F=%02X  ALU_Op_r=%X BusA=%02X BusB=%02X F_Out=%02X F_Out_r=%02X Save_ALU=%d\n",
                   pc, m, t, t_res, ir, f, alu_op_r, bus_a, bus_b, f_out, f_out_r, save_alu);

            // Stop after HALT
            if (ir == 0x76) {
                printf("\n=== HALT reached ===\n");
                break;
            }
        }
    }

    printf("\nFinal F register: 0x%02X\n", dut->dbg_cpu_f);
    printf("  Z=%d N=%d H=%d C=%d\n",
           (dut->dbg_cpu_f >> 7) & 1,
           (dut->dbg_cpu_f >> 6) & 1,
           (dut->dbg_cpu_f >> 5) & 1,
           (dut->dbg_cpu_f >> 4) & 1);

    delete dut;
    return 0;
}
