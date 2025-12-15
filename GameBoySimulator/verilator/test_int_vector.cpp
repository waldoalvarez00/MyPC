// Debug interrupt vector fetch timing
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Interrupt Vector Debug ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    const char* rom_path = argc > 1 ? argv[1] : "test_roms/cpu_instrs/individual/02-interrupts.gb";
    FILE* f = fopen(rom_path, "rb");
    if (!f) { printf("Cannot open %s\n", rom_path); return 1; }
    fseek(f, 0, SEEK_END);
    size_t rom_size = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t* rom = new uint8_t[rom_size];
    fread(rom, 1, rom_size, f);
    fclose(f);

    sdram->loadBinary(0, rom, rom_size);

    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;
    boot[i++] = 0x3E; boot[i++] = 0x91;
    boot[i++] = 0xE0; boot[i++] = 0x40;
    boot[i++] = 0x06; boot[i++] = 0x00;
    boot[i++] = 0x0E; boot[i++] = 0x13;
    boot[i++] = 0x16; boot[i++] = 0x00;
    boot[i++] = 0x1E; boot[i++] = 0xD8;
    boot[i++] = 0x26; boot[i++] = 0x01;
    boot[i++] = 0x2E; boot[i++] = 0x4D;
    boot[i++] = 0xD5;
    boot[i++] = 0x16; boot[i++] = 0x01;
    boot[i++] = 0x1E; boot[i++] = 0xB0;
    boot[i++] = 0xD5;
    boot[i++] = 0xF1;
    boot[i++] = 0xD1;
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = boot[addr] | ((uint16_t)boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);
    for (int w = 0; w < 5000 && !dut->dbg_cart_ready; w++) {
        tick_with_sdram(dut, sdram);
    }

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    int cycles = 0;
    int max_cycles = 30000000;
    uint8_t prev_intcycle_n = 1;
    bool tracing = false;
    int trace_count = 0;

    printf("Running test...\n\n");

    while (cycles < max_cycles) {
        tick_with_sdram(dut, sdram);
        cycles++;

        // Detect IntCycle start
        if (prev_intcycle_n && !dut->dbg_intcycle_n) {
            printf("\n=== INTCYCLE START at cycle %d ===\n", cycles);
            printf("PC=0x%04X IE=0x%02X IF=0x%02X\n",
                   dut->dbg_cpu_pc, dut->dbg_ie_r, dut->dbg_if_r);
            tracing = true;
            trace_count = 0;
        }

        // Trace during IntCycle
        if (tracing) {
            trace_count++;
            printf("[%d.%03d] intcycle_n=%d irq_ack=%d PC=0x%04X mcycle=0x%02X tstate=0x%02X IR=0x%02X\n",
                   cycles, trace_count, dut->dbg_intcycle_n, dut->dbg_irq_ack,
                   dut->dbg_cpu_pc, dut->dbg_cpu_mcycle, dut->dbg_cpu_tstate, dut->dbg_cpu_ir);

            if (trace_count > 100 || dut->dbg_intcycle_n) {
                printf("=== INTCYCLE END ===\n\n");
                tracing = false;
                break;  // Stop after first interrupt
            }
        }

        prev_intcycle_n = dut->dbg_intcycle_n;

        if (cycles % 10000000 == 0) {
            printf("\n[%dM cycles, PC=0x%04X]\n", cycles/1000000, dut->dbg_cpu_pc);
        }
    }

    printf("\nFinal PC=0x%04X\n", dut->dbg_cpu_pc);

    delete[] rom;
    delete sdram;
    delete dut;
    return 0;
}
