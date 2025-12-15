// Debug test for WRAM write issues
// Traces memory writes during the test ROM copy loop
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

    printf("=== WRAM Write Debug Test ===\n\n");

    // Load the actual Blargg ROM
    std::vector<uint8_t> rom;
    FILE* f = fopen("cpu_instrs/individual/01-special.gb", "rb");
    if (!f) {
        printf("ERROR: Cannot open cpu_instrs/individual/01-special.gb\n");
        return 1;
    }
    fseek(f, 0, SEEK_END);
    size_t rom_size = ftell(f);
    fseek(f, 0, SEEK_SET);
    rom.resize(rom_size);
    fread(rom.data(), 1, rom_size, f);
    fclose(f);
    printf("Loaded ROM: %zu bytes\n", rom_size);

    // Create DUT and SDRAM model
    Vtop* dut = new Vtop;
    MisterSDRAMModel sdram(8, INTERFACE_NATIVE_SDRAM);
    sdram.cas_latency = 2;
    sdram.debug = false;

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

    // Load boot ROM
    std::vector<uint8_t> boot(256, 0);
    boot[0x00] = 0xC3;  // JP 0x0100
    boot[0x01] = 0x00;
    boot[0x02] = 0x01;

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

    printf("Running simulation to find WRAM writes...\n\n");

    // Access the GB module and CPU
    auto* top_module = dut->top;
    auto* gb_module = top_module->gameboy;
    auto* cpu_module = gb_module->cpu;
    auto* cpu_core = cpu_module->i_tv80_core;

    uint16_t prev_pc = 0;
    int write_count = 0;
    int instr_count = 0;
    bool copy_loop_active = false;
    bool logging = false;

    // Track last written WRAM addresses for verification
    uint8_t wram_shadow[0x2000] = {0};  // 8KB shadow

    for (int i = 0; i < 2000000 && instr_count < 20000; i++) {
        run_cycles_with_sdram(dut, &sdram, 1);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t cpu_m1_n = cpu_module->__PVT__M1_n;

        // Count instructions on M1 cycles
        if (cpu_m1_n == 0 && pc != prev_pc) {
            instr_count++;
            prev_pc = pc;

            // Start logging when we reach the copy loop setup
            if (pc == 0x0200 && !logging) {
                printf("\n=== Reached copy loop setup at PC=0x0200 ===\n");
                logging = true;
            }
        }

        // Monitor writes to WRAM region (0xC000-0xDFFF)
        uint16_t cpu_addr = cpu_module->__PVT__A;
        uint8_t cpu_wr_n = cpu_module->__PVT__WR_n;
        uint8_t cpu_do = cpu_module->__PVT__DO;

        // Also get tv80_core internal signals
        uint16_t core_addr = cpu_core->__PVT__A;
        uint8_t core_write = cpu_core->__PVT__write;

        // Also get other useful signals
        uint8_t mcycle = cpu_core->__PVT__mcycle;
        uint8_t tstate = cpu_core->__PVT__tstate;
        uint8_t acc = cpu_core->ACC;
        uint8_t ir = cpu_core->IR;
        uint8_t dout = cpu_core->__PVT__dout;
        uint8_t dout_next = cpu_core->__PVT__dout_next;  // New combinational output
        uint8_t busb = cpu_core->__PVT__BusB;
        uint8_t busb_next = cpu_core->__PVT__BusB_next;
        uint8_t auto_wait = cpu_core->__PVT__Auto_Wait_t1;
        uint8_t clken = cpu_core->ClkEn;

        // Check for any write (using tv80_core's write signal)
        static int total_writes = 0;
        if (core_write == 1) {  // tv80_core's write is active HIGH
            total_writes++;
            // Print first 50 and around copy loop
            if (total_writes < 50 || (instr_count >= 6560 && instr_count <= 6580 && total_writes < 500)) {
                printf("Write #%d: [$%04X] dout=%02X dout_next=%02X DO=%02X BusB_next=%02X A=%02X IR=%02X M%02X T%02X\n",
                       total_writes, core_addr, dout, dout_next, cpu_do, busb_next, acc, ir, mcycle, tstate);
            }

            // Check for write to WRAM region (0xC000-0xDFFF) using core address
            if ((core_addr & 0xE000) == 0xC000) {
                uint16_t wram_offset = core_addr & 0x1FFF;

                if (logging && write_count < 50) {
                    printf("  -> WRAM Write #%d: [$%04X] = $%02X\n",
                           write_count, core_addr, cpu_do);
                }

                // Track in shadow
                wram_shadow[wram_offset] = cpu_do;
                write_count++;
            }
        }

        // After we've done some writes, check if they persisted
        if (instr_count == 18000) {
            printf("\n=== WRAM Shadow verification at 0xC000 ===\n");
            printf("Expected at 0xC000: C3 20 C2 (JP $C220)\n");
            printf("Shadow at 0xC000:   %02X %02X %02X\n",
                   wram_shadow[0x0000], wram_shadow[0x0001], wram_shadow[0x0002]);

            // Try to read what the GB thinks is at 0xC000
            // This would require accessing internal WRAM...
        }

        // Stop after reaching jump to WRAM
        if (pc == 0xC000 && instr_count > 1000) {
            printf("\n=== Jumped to WRAM at 0xC000 ===\n");
            printf("Total WRAM writes observed: %d\n", write_count);
            printf("Shadow at 0xC000: %02X %02X %02X %02X\n",
                   wram_shadow[0x0000], wram_shadow[0x0001],
                   wram_shadow[0x0002], wram_shadow[0x0003]);
            break;
        }
    }

    printf("\nTotal instructions: %d\n", instr_count);
    printf("Total writes observed (any address): %d\n", 0);  // placeholder
    printf("Total WRAM writes: %d\n", write_count);

    delete dut;
    return 0;
}
