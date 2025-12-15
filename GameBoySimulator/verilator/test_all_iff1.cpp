// Trace ALL IFF1 changes during test
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>
#include <string>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== All IFF1 Changes Test ===\n");

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
    int iff1_set_count = 0;
    int iff1_clear_count = 0;
    int interrupt_count = 0;

    printf("Running test...\n\n");

    while (cycles < max_cycles && !test_complete) {
        tick_with_sdram(dut, sdram);
        cycles++;

        // Track IFF1 changes
        if (prev_iff1 != dut->dbg_cpu_iff1) {
            if (dut->dbg_cpu_iff1) {
                iff1_set_count++;
                if (iff1_set_count <= 10) {
                    printf("[%d] IFF1 SET: PC=0x%04X IR=0x%02X IE=0x%02X IF=0x%02X\n",
                           cycles, dut->dbg_cpu_pc, dut->dbg_cpu_ir,
                           dut->dbg_ie_r, dut->dbg_if_r);
                }
            } else {
                iff1_clear_count++;
                if (iff1_clear_count <= 10) {
                    printf("[%d] IFF1 CLR: PC=0x%04X IR=0x%02X IE=0x%02X IF=0x%02X intcycle_n=%d\n",
                           cycles, dut->dbg_cpu_pc, dut->dbg_cpu_ir,
                           dut->dbg_ie_r, dut->dbg_if_r, dut->dbg_intcycle_n);
                }
            }
        }

        // Track interrupt starts
        if (prev_intcycle_n && !dut->dbg_intcycle_n) {
            interrupt_count++;
            if (interrupt_count <= 10) {
                printf("[%d] INT START: PC=0x%04X IE=0x%02X IF=0x%02X IFF1=%d\n",
                       cycles, dut->dbg_cpu_pc, dut->dbg_ie_r, dut->dbg_if_r,
                       dut->dbg_cpu_iff1);
            }
        }
        if (!prev_intcycle_n && dut->dbg_intcycle_n) {
            if (interrupt_count <= 10) {
                printf("[%d] INT END: PC=0x%04X IE=0x%02X IF=0x%02X\n",
                       cycles, dut->dbg_cpu_pc, dut->dbg_ie_r, dut->dbg_if_r);
            }
        }

        prev_iff1 = dut->dbg_cpu_iff1;
        prev_intcycle_n = dut->dbg_intcycle_n;
        prev_if_r = dut->dbg_if_r;

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
                }
            }
        }
        prev_cpu_wr_n = dut->dbg_cpu_wr_n;

        if ((serial_output.find("Passed") != std::string::npos ||
             serial_output.find("Failed") != std::string::npos) &&
            (cycles - last_serial_cycle) > 500000) {
            test_complete = true;
        }

        if (cycles % 10000000 == 0) {
            printf("\n[%dM cycles, PC=0x%04X, IFF1_sets=%d, IFF1_clrs=%d, INTs=%d]\n",
                   cycles/1000000, dut->dbg_cpu_pc, iff1_set_count, iff1_clear_count, interrupt_count);
        }
    }

    printf("\n\n=== Results ===\n");
    printf("Serial output: %s\n", serial_output.c_str());
    printf("IFF1 set count: %d\n", iff1_set_count);
    printf("IFF1 clear count: %d\n", iff1_clear_count);
    printf("Interrupt count: %d\n", interrupt_count);

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
