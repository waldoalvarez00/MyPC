// Trace full interrupt sequence during EI test
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>
#include <string>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== EI Sequence Test ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Load ROM
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

    std::string serial_output;
    uint8_t sb_value = 0;
    uint8_t prev_cpu_wr_n = 1;
    int cycles = 0;
    int max_cycles = 60000000;
    int last_serial_cycle = 0;
    bool test_complete = false;

    uint8_t prev_iff1 = 0;
    uint8_t prev_intcycle_n = 1;
    uint8_t prev_if_r = 0;
    uint16_t prev_pc = 0;
    uint8_t prev_ir = 0;

    // Track all IFF1 and intcycle changes
    int event_count = 0;
    bool ei_section = false;
    int ei_event_start = 0;

    printf("Running test...\n");
    printf("Waiting for EI test section...\n\n");

    while (cycles < max_cycles && !test_complete) {
        tick_with_sdram(dut, sdram);
        cycles++;

        // Serial capture
        bool cpu_write = (prev_cpu_wr_n == 1 && dut->dbg_cpu_wr_n == 0 && dut->dbg_cpu_mreq_n == 0);
        if (cpu_write) {
            uint16_t addr = dut->dbg_cpu_addr;
            uint8_t data = dut->dbg_cpu_do;

            if (addr == 0xFF01) {
                sb_value = data;
            } else if (addr == 0xFF02) {
                if (data & 0x80) {
                    if (sb_value >= 0x20 && sb_value < 0x7F) {
                        putchar(sb_value);
                        fflush(stdout);
                    } else if (sb_value == '\n') {
                        putchar('\n');
                        fflush(stdout);
                    }
                    serial_output += (char)sb_value;
                    last_serial_cycle = cycles;

                    // Check if we're entering EI test section
                    if (serial_output.find("EI\n") != std::string::npos && !ei_section) {
                        ei_section = true;
                        printf("\n=== Entering EI test section ===\n");
                        ei_event_start = event_count;
                    }
                }
            }
        }
        prev_cpu_wr_n = dut->dbg_cpu_wr_n;

        // Track events during EI section
        bool iff1_changed = (prev_iff1 != dut->dbg_cpu_iff1);
        bool intcycle_changed = (prev_intcycle_n != dut->dbg_intcycle_n);
        bool if_changed = (prev_if_r != dut->dbg_if_r);

        if (ei_section && (iff1_changed || intcycle_changed || if_changed)) {
            event_count++;
            if (event_count - ei_event_start < 100) {  // Limit output
                printf("[%d] PC=0x%04X IR=0x%02X IFF1=%d->%d intcycle_n=%d->%d IF=0x%02X->0x%02X IE=0x%02X",
                       cycles, dut->dbg_cpu_pc, dut->dbg_cpu_ir,
                       prev_iff1, dut->dbg_cpu_iff1,
                       prev_intcycle_n, dut->dbg_intcycle_n,
                       prev_if_r, dut->dbg_if_r,
                       dut->dbg_ie_r);
                if (iff1_changed) printf(" [IFF1]");
                if (intcycle_changed) printf(" [INTCYCLE]");
                if (if_changed) printf(" [IF]");
                printf("\n");
            }
        }

        prev_iff1 = dut->dbg_cpu_iff1;
        prev_intcycle_n = dut->dbg_intcycle_n;
        prev_if_r = dut->dbg_if_r;
        prev_pc = dut->dbg_cpu_pc;
        prev_ir = dut->dbg_cpu_ir;

        if ((serial_output.find("Passed") != std::string::npos ||
             serial_output.find("Failed") != std::string::npos) &&
            (cycles - last_serial_cycle) > 500000) {
            test_complete = true;
        }

        if (cycles % 10000000 == 0) {
            printf("\n[%dM cycles, PC=0x%04X, IE=0x%02X, IF=0x%02X, IFF1=%d, events=%d]\n",
                   cycles/1000000, dut->dbg_cpu_pc, dut->dbg_ie_r, dut->dbg_if_r,
                   dut->dbg_cpu_iff1, event_count);
        }
    }

    printf("\n\n=== Results ===\n");
    printf("Serial output: %s\n", serial_output.c_str());
    printf("Total events: %d\n", event_count);

    bool passed = serial_output.find("Passed") != std::string::npos;
    bool failed = serial_output.find("Failed") != std::string::npos;

    if (passed) printf("TEST PASSED!\n");
    else if (failed) printf("TEST FAILED!\n");
    else printf("Test status unclear\n");

    delete[] rom;
    delete sdram;
    delete dut;
    return passed ? 0 : 1;
}
