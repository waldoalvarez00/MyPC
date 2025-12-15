// Trace DAA operations early in Blargg test (around cycle 150K where failures occur)
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>
#include <string>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Blargg DAA Early Trace ===\n");

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
    int max_cycles = 200000000;  // Run up to 200M cycles like the full test
    int last_serial_cycle = 0;
    bool test_complete = false;

    printf("Running test with early DAA tracing...\n\n");

    // Track last few DAA operations before serial output
    struct DAARecord {
        int cycle;
        uint16_t pc;
        uint8_t a_before, f_before;
        uint8_t a_after, f_after;
    };
    DAARecord daa_history[100];
    int daa_history_idx = 0;
    int daa_count = 0;

    // Start tracing immediately
    bool tracing_daa = true;
    bool found_hex_output = false;
    int hex_start_cycle = 0;

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

                    if (c >= 0x20 && c < 0x7F) {
                        putchar(c);
                        fflush(stdout);
                    } else if (c == '\n') {
                        putchar('\n');
                        fflush(stdout);
                    }

                    // Detect hex digit output (the failure results)
                    if (!found_hex_output && ((c >= 'A' && c <= 'F') || (c >= '0' && c <= '9'))) {
                        found_hex_output = true;
                        hex_start_cycle = cycles;
                        printf("\n\n=== HEX OUTPUT STARTED at cycle %d ===\n", cycles);
                        printf("Last %d DAA operations before failure:\n", daa_history_idx);
                        for (int j = 0; j < daa_history_idx && j < 100; j++) {
                            DAARecord& r = daa_history[j];
                            printf("  [cycle %d] PC=%04X: A=%02X F=%02X -> A=%02X F=%02X\n",
                                   r.cycle, r.pc, r.a_before, r.f_before, r.a_after, r.f_after);
                        }
                        printf("=================================\n\n");
                    }

                    last_serial_cycle = cycles;

                    if (serial_output.find("Passed") != std::string::npos ||
                        serial_output.find("Failed") != std::string::npos) {
                        if ((cycles - last_serial_cycle) > 10000) {
                            test_complete = true;
                        }
                    }
                }
            }
        }

        // Track DAA instructions (opcode 0x27)
        uint8_t ir = dut->dbg_cpu_ir;
        if (ir == 0x27 && tracing_daa) {
            uint8_t a_before = dut->dbg_cpu_acc;
            uint8_t f_before = dut->dbg_cpu_f;
            uint16_t pc = dut->dbg_cpu_pc;

            // Run a few cycles to let DAA complete
            for (int j = 0; j < 16; j++) {
                tick_with_sdram(dut, sdram);
                cycles++;
            }

            uint8_t a_after = dut->dbg_cpu_acc;
            uint8_t f_after = dut->dbg_cpu_f;

            // Store in circular buffer
            daa_history[daa_history_idx % 100].cycle = cycles;
            daa_history[daa_history_idx % 100].pc = pc;
            daa_history[daa_history_idx % 100].a_before = a_before;
            daa_history[daa_history_idx % 100].f_before = f_before;
            daa_history[daa_history_idx % 100].a_after = a_after;
            daa_history[daa_history_idx % 100].f_after = f_after;
            daa_history_idx++;
            daa_count++;

            // Print DAA operations right before hex output
            if (found_hex_output && cycles < hex_start_cycle + 5000) {
                printf("[cycle %d] DAA at PC=%04X: A=%02X F=%02X (Z=%d N=%d H=%d C=%d) -> A=%02X F=%02X\n",
                       cycles, pc, a_before, f_before,
                       (f_before >> 7) & 1, (f_before >> 6) & 1,
                       (f_before >> 5) & 1, (f_before >> 4) & 1,
                       a_after, f_after);
            }
        }

        // Stop tracing after hex output to speed up
        if (found_hex_output && cycles > hex_start_cycle + 10000) {
            tracing_daa = false;
        }

        prev_cpu_wr_n = dut->dbg_cpu_wr_n;

        // Check for test completion
        if (serial_output.find("Failed") != std::string::npos ||
            serial_output.find("Passed") != std::string::npos) {
            if ((cycles - last_serial_cycle) > 50000) {
                test_complete = true;
            }
        }

        if (cycles % 5000000 == 0) {
            printf("\n[%dM cycles, PC=0x%04X, DAA count=%d]\n", cycles/1000000, dut->dbg_cpu_pc, daa_count);
        }
    }

    printf("\n\n=== Final Serial Output ===\n%s\n", serial_output.c_str());
    printf("Total DAA operations traced: %d\n", daa_count);

    bool passed = serial_output.find("Passed") != std::string::npos;
    printf("\nTest %s\n", passed ? "PASSED" : "FAILED");

    delete[] rom;
    delete sdram;
    delete dut;
    return passed ? 0 : 1;
}
