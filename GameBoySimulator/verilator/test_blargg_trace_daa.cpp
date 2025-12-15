// Trace Blargg test around DAA output
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>
#include <string>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Blargg DAA Trace ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    const char* rom_path = argc > 1 ? argv[1] : "../blargg_tests/gb-test-roms-master/cpu_instrs/individual/01-special.gb";
    FILE* f = fopen(rom_path, "rb");
    if (!f) { printf("Cannot open %s\n", rom_path); return 1; }
    fseek(f, 0, SEEK_END);
    size_t rom_size = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t* rom = new uint8_t[rom_size];
    fread(rom, 1, rom_size, f);
    fclose(f);
    printf("Loaded ROM: %zu bytes\n", rom_size);

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
    printf("cart_ready = %d\n", dut->dbg_cart_ready);

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    std::string serial_output;
    uint8_t sb_value = 0;
    uint8_t prev_cpu_wr_n = 1;
    int cycles = 0;
    int max_cycles = 200000000;
    int last_serial_cycle = 0;
    bool test_complete = false;

    printf("Running test...\n\n");

    // Only trace DAA near the failure point (around 140M-160M cycles)
    bool in_hex_output = false;
    int daa_trace_count = 0;
    int daa_trace_start = -1;
    bool tracing_enabled = false;

    while (cycles < max_cycles && !test_complete) {
        tick_with_sdram(dut, sdram);
        cycles++;

        bool cpu_write = (prev_cpu_wr_n == 1 && dut->dbg_cpu_wr_n == 0 && dut->dbg_cpu_mreq_n == 0);

        if (cpu_write) {
            uint16_t addr = dut->dbg_cpu_addr;
            uint8_t data = dut->dbg_cpu_do;

            if (addr == 0xFF01) {
                sb_value = data;
            }
            else if (addr == 0xFF02) {
                if (data & 0x80) {
                    char c = (char)sb_value;
                    serial_output += c;

                    // Print immediately
                    if (c >= 0x20 && c < 0x7F) {
                        putchar(c);
                        fflush(stdout);
                    } else if (c == '\n') {
                        putchar('\n');
                        fflush(stdout);
                    }

                    // Start tracing when we see hex digits (A-F or 0-9)
                    if (!in_hex_output && ((c >= 'A' && c <= 'F') || (c >= '0' && c <= '9'))) {
                        in_hex_output = true;
                        daa_trace_start = cycles;
                        printf("\n[Starting DAA trace at cycle %d, char '%c']\n", cycles, c);
                    }

                    last_serial_cycle = cycles;

                    if (serial_output.find("Passed") != std::string::npos ||
                        serial_output.find("Failed") != std::string::npos) {
                        if ((cycles - last_serial_cycle) > 1000000) {
                            test_complete = true;
                        }
                    }
                }
            }
        }

        // Enable tracing only near the failure point (around 152M cycles to catch A0A0A0D2)
        if (cycles == 152000000) {
            tracing_enabled = true;
            printf("\n[Enabling trace at cycle 148M]\n");
        }

        // Trace serial writes and nearby instructions
        if (tracing_enabled && daa_trace_count < 2000) {
            // Trace serial writes
            if (cpu_write) {
                uint16_t addr = dut->dbg_cpu_addr;
                uint8_t data = dut->dbg_cpu_do;
                if (addr == 0xFF01) {
                    printf("[cycle %d] SERIAL SB write: %02X '%c' PC=%04X A=%02X F=%02X\n",
                           cycles, data, (data >= 0x20 && data < 0x7F) ? data : '.',
                           dut->dbg_cpu_pc, dut->dbg_cpu_acc, dut->dbg_cpu_f);
                    daa_trace_count++;
                }
                else if (addr == 0xFF02 && (data & 0x80)) {
                    printf("[cycle %d] SERIAL SC trigger PC=%04X A=%02X F=%02X (SB was 0x%02X)\n",
                           cycles, dut->dbg_cpu_pc, dut->dbg_cpu_acc, dut->dbg_cpu_f, sb_value);
                    daa_trace_count++;
                }
            }

            // Also trace DAA instructions
            uint8_t ir = dut->dbg_cpu_ir;
            if (ir == 0x27) {
                printf("[cycle %d] DAA: PC=%04X A=%02X F=%02X (Z=%d N=%d H=%d C=%d) -> ",
                       cycles, dut->dbg_cpu_pc, dut->dbg_cpu_acc, dut->dbg_cpu_f,
                       (dut->dbg_cpu_f >> 7) & 1, (dut->dbg_cpu_f >> 6) & 1,
                       (dut->dbg_cpu_f >> 5) & 1, (dut->dbg_cpu_f >> 4) & 1);

                for (int j = 0; j < 16; j++) {
                    tick_with_sdram(dut, sdram);
                    cycles++;
                }

                printf("A=%02X F=%02X\n", dut->dbg_cpu_acc, dut->dbg_cpu_f);
                daa_trace_count++;
            }
        }

        // Stop DAA tracing after test completes
        if (serial_output.find("Failed") != std::string::npos ||
            serial_output.find("Passed") != std::string::npos) {
            if (in_hex_output) {
                in_hex_output = false;
                printf("[DAA trace ended, found result marker]\n");
            }
            if ((cycles - last_serial_cycle) > 1000000) {
                test_complete = true;
            }
        }

        prev_cpu_wr_n = dut->dbg_cpu_wr_n;

        if (cycles % 50000000 == 0) {
            printf("\n[%dM cycles, PC=0x%04X]\n", cycles/1000000, dut->dbg_cpu_pc);
        }
    }

    printf("\n\n=== Final Serial Output ===\n%s\n", serial_output.c_str());

    bool passed = serial_output.find("Passed") != std::string::npos;
    printf("\nTest %s\n", passed ? "PASSED" : "FAILED");

    delete[] rom;
    delete sdram;
    delete dut;
    return passed ? 0 : 1;
}
