// Detailed DAA trace - capture ALL DAA operations with full context
#include <verilated.h>
#include "Vtop.h"
#include "Vtop_top.h"
#include "Vtop_gb.h"
#include "Vtop_dpram__A7.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>
#include <array>

struct DAATrace {
    int cycle;
    uint16_t pc;
    uint8_t a_in, f_in;
    uint8_t a_out, f_out;
    uint8_t a_exp, f_exp;
    bool mismatch;
};

static uint32_t crc32_update(uint32_t crc, uint8_t byte) {
    crc ^= byte;
    for (int i = 0; i < 8; i++) {
        if (crc & 1) crc = (crc >> 1) ^ 0xEDB88320u;
        else crc >>= 1;
    }
    return crc;
}

static uint16_t ref_daa(uint8_t a, uint8_t f) {
    int n = (f >> 6) & 1;
    int h = (f >> 5) & 1;
    int c = (f >> 4) & 1;

    int result = a;
    int carry_out = c;

    if (n == 0) {
        if (h || (result & 0x0F) > 9) {
            result += 0x06;
        }
        if (c || result > 0x9F) {
            result += 0x60;
            carry_out = 1;
        }
    } else {
        if (h) {
            result -= 0x06;
        }
        if (c) {
            result -= 0x60;
        }
    }

    result &= 0xFF;
    int z = (result == 0) ? 1 : 0;
    uint8_t flags_out = (z << 7) | (n << 6) | (0 << 5) | (carry_out << 4);
    return (uint16_t)((flags_out << 8) | result);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Detailed DAA Trace ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    const char* rom_path = argc > 1 ? argv[1] : "blargg_tests/gb-test-roms-master/cpu_instrs/individual/01-special.gb";
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
    std::vector<DAATrace> daa_traces;
    uint8_t sb_value = 0;
    uint8_t prev_cpu_wr_n = 1;
    int cycles = 0;
    int max_cycles = 200000000;
    int last_serial_cycle = 0;
    bool test_complete = false;
    bool found_failure = false;
    int failure_cycle = 0;

    printf("Running test with DAA tracing...\n\n");

    // Track when we're in the DAA test section (PC around 0xC300-C400)
    bool in_daa_test = false;
    uint8_t last_ir = 0;
    size_t daa_mismatches = 0;
    std::array<uint32_t, 16> f_in_hist{};
    std::array<std::array<bool, 256>, 16> seen{};
    uint32_t sw_crc = 0xFFFFFFFFu; // matches checksum storage format in Blargg tests
    bool sw_crc_seeded_from_hw = false;
    uint32_t hw_crc_at_first_daa = 0;
    bool crc_mismatch_found = false;
    size_t crc_mismatch_index = 0;
    uint32_t crc_hw = 0;

    while (cycles < max_cycles && !test_complete) {
        tick_with_sdram(dut, sdram);
        cycles++;

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t ir = dut->dbg_cpu_ir;

        // Detect entering DAA test region
        if (pc >= 0xC300 && pc <= 0xC400) {
            in_daa_test = true;
        }

        // Track DAA instructions - look for IR=0x27 at start of instruction
        if (ir == 0x27 && last_ir != 0x27) {
            if (!sw_crc_seeded_from_hw) {
                uint32_t hw0 = (uint32_t)dut->top->gameboy->zpram->mem[0]
                             | ((uint32_t)dut->top->gameboy->zpram->mem[1] << 8)
                             | ((uint32_t)dut->top->gameboy->zpram->mem[2] << 16)
                             | ((uint32_t)dut->top->gameboy->zpram->mem[3] << 24);
                hw_crc_at_first_daa = hw0;
                sw_crc = hw0;
                sw_crc_seeded_from_hw = true;
                printf("\n[CRC SEED] At start of first DAA: hw=0x%08X\n", hw0);
                if (hw0 != 0xFFFFFFFFu) {
                    printf("[CRC SEED] WARNING: expected 0xFFFFFFFF at start of DAA test\n");
                }
            }

            // By the time we fetch the next DAA, the previous iteration's update_crc calls
            // should have completed and the checksum in HRAM should match our software CRC.
            if (!daa_traces.empty()) {
                uint32_t hw = (uint32_t)dut->top->gameboy->zpram->mem[0]
                            | ((uint32_t)dut->top->gameboy->zpram->mem[1] << 8)
                            | ((uint32_t)dut->top->gameboy->zpram->mem[2] << 16)
                            | ((uint32_t)dut->top->gameboy->zpram->mem[3] << 24);
                if (hw != sw_crc && !crc_mismatch_found) {
                    crc_mismatch_found = true;
                    crc_mismatch_index = daa_traces.size();
                    crc_hw = hw;
                    printf("\n[CRC MISMATCH] At start of DAA #%zu: hw=0x%08X sw=0x%08X\n",
                           crc_mismatch_index, hw, sw_crc);
                }
            }

            uint8_t a_in = dut->dbg_cpu_acc;
            uint8_t f_in = dut->dbg_cpu_f;

            // Run until DAA completes (IR changes)
            int wait = 0;
            while (dut->dbg_cpu_ir == 0x27 && wait < 100) {
                tick_with_sdram(dut, sdram);
                cycles++;
                wait++;
            }

            uint8_t a_out = dut->dbg_cpu_acc;
            uint8_t f_out = dut->dbg_cpu_f;

            f_in_hist[(f_in >> 4) & 0xF]++;
            seen[(f_in >> 4) & 0xF][a_in] = true;

            uint16_t ref = ref_daa(a_in, f_in);
            uint8_t a_exp = ref & 0xFF;
            uint8_t f_exp = (ref >> 8) & 0xF0;
            bool mismatch = (a_out != a_exp) || ((f_out & 0xF0) != f_exp);
            if (mismatch) {
                daa_mismatches++;
            }

            // Store trace
            DAATrace t;
            t.cycle = cycles;
            t.pc = pc;
            t.a_in = a_in;
            t.f_in = f_in;
            t.a_out = a_out;
            t.f_out = f_out;
            t.a_exp = a_exp;
            t.f_exp = f_exp;
            t.mismatch = mismatch;
            daa_traces.push_back(t);

            // Software CRC update for what the ROM does after each DAA:
            //   push af
            //   call update_crc   ; A (DAA result)
            //   pop hl
            //   ld a,l            ; F (DAA flags)
            //   call update_crc
            sw_crc = crc32_update(sw_crc, a_out);
            sw_crc = crc32_update(sw_crc, (uint8_t)(f_out & 0xFF));

            // Limit stored traces
            if (daa_traces.size() > 5000) {
                daa_traces.erase(daa_traces.begin());
            }
        }
        last_ir = ir;

        // Serial output capture
        bool cpu_write = (prev_cpu_wr_n == 1 && dut->dbg_cpu_wr_n == 0 && dut->dbg_cpu_mreq_n == 0);
        if (cpu_write) {
            uint16_t addr = dut->dbg_cpu_addr;
            uint8_t data = dut->dbg_cpu_do;

            if (addr == 0xFF01) {
                sb_value = data;
            }
            else if (addr == 0xFF02 && (data & 0x80)) {
                char c = (char)sb_value;
                serial_output += c;

                if (c >= 0x20 && c < 0x7F) {
                    putchar(c);
                    fflush(stdout);
                } else if (c == '\n') {
                    putchar('\n');
                    fflush(stdout);
                }

                // Detect hex output (failure marker)
                if (!found_failure && ((c >= 'A' && c <= 'F') || (c >= '0' && c <= '9'))) {
                    found_failure = true;
                    failure_cycle = cycles;
                    printf("\n\n=== FAILURE DETECTED at cycle %d ===\n", cycles);
                    printf("Last 50 DAA operations before failure:\n");
                    int start = (int)daa_traces.size() - 50;
                    if (start < 0) start = 0;
                    for (size_t j = start; j < daa_traces.size(); j++) {
                        DAATrace& t = daa_traces[j];
                        // Decode GB flags: Z=7, N=6, H=5, C=4
                        int z_in = (t.f_in >> 7) & 1;
                        int n_in = (t.f_in >> 6) & 1;
                        int h_in = (t.f_in >> 5) & 1;
                        int c_in = (t.f_in >> 4) & 1;
                        int z_out = (t.f_out >> 7) & 1;
                        int n_out = (t.f_out >> 6) & 1;
                        int h_out = (t.f_out >> 5) & 1;
                        int c_out = (t.f_out >> 4) & 1;
                        printf("  [%d] PC=%04X: A=%02X F=%02X (N=%d H=%d C=%d) -> A=%02X F=%02X (Z=%d N=%d H=%d C=%d)\n",
                               t.cycle, t.pc, t.a_in, t.f_in, n_in, h_in, c_in,
                               t.a_out, t.f_out, z_out, n_out, h_out, c_out);
                    }
                    printf("=== END OF DAA TRACE ===\n\n");
                }

                last_serial_cycle = cycles;
            }
        }
        prev_cpu_wr_n = dut->dbg_cpu_wr_n;

        // Check for test completion
        if (serial_output.find("Failed") != std::string::npos ||
            serial_output.find("Passed") != std::string::npos) {
            if ((cycles - last_serial_cycle) > 1000000) {
                test_complete = true;
            }
        }

        if (cycles % 10000000 == 0) {
            printf("\n[%dM cycles, PC=0x%04X, DAA traces=%zu]\n",
                   cycles/1000000, pc, daa_traces.size());
        }

        if (crc_mismatch_found && daa_traces.size() > crc_mismatch_index + 5) {
            // We've identified a deterministic checksum mismatch point; no need to run longer here.
            test_complete = true;
        }
    }

    printf("\n\n=== Final Serial Output ===\n%s\n", serial_output.c_str());
    printf("Total DAA operations traced: %zu\n", daa_traces.size());
    printf("DAA mismatches vs reference: %zu\n", daa_mismatches);

    printf("DAA input F histogram (by high nibble):\n");
    for (int hi = 0; hi < 16; hi++) {
        printf("  F=0x%X0: %u\n", hi, f_in_hist[hi]);
    }

    size_t missing = 0;
    for (int hi = 0; hi < 16; hi++) {
        for (int a = 0; a < 256; a++) {
            if (!seen[hi][a]) missing++;
        }
    }
    printf("Missing (F_hi,A) combinations: %zu\n", missing);
    if (crc_mismatch_found) {
        printf("CRC mismatch observed: hw=0x%08X sw=0x%08X at start of DAA #%zu\n",
               crc_hw, sw_crc, crc_mismatch_index);
    }

    // Inspect the checksum stored in HRAM (dp=$FF80, checksum = dp+0..3).
    // In gb.v this is the 'zpram' block (0xFF80-0xFFFE), index 0 corresponds to 0xFF80.
    uint8_t chk0 = dut->top->gameboy->zpram->mem[0];
    uint8_t chk1 = dut->top->gameboy->zpram->mem[1];
    uint8_t chk2 = dut->top->gameboy->zpram->mem[2];
    uint8_t chk3 = dut->top->gameboy->zpram->mem[3];
    uint32_t checksum_le = (uint32_t)chk0 | ((uint32_t)chk1 << 8) | ((uint32_t)chk2 << 16) | ((uint32_t)chk3 << 24);
    uint32_t printed_crc = checksum_le ^ 0xFFFFFFFFu;
    printf("HRAM checksum bytes: %02X %02X %02X %02X (printed CRC would be 0x%08X)\n",
           chk0, chk1, chk2, chk3, printed_crc);

    if (daa_mismatches) {
        printf("\n=== First 25 DAA mismatches ===\n");
        int printed = 0;
        for (const auto& t : daa_traces) {
            if (!t.mismatch) continue;
            int z_in = (t.f_in >> 7) & 1;
            int n_in = (t.f_in >> 6) & 1;
            int h_in = (t.f_in >> 5) & 1;
            int c_in = (t.f_in >> 4) & 1;
            printf("PC=%04X: A=%02X F=%02X (Z=%d N=%d H=%d C=%d) -> got A=%02X F=%02X, exp A=%02X F=%02X\n",
                   t.pc, t.a_in, t.f_in, z_in, n_in, h_in, c_in,
                   t.a_out, t.f_out & 0xF0, t.a_exp, t.f_exp);
            if (++printed >= 25) break;
        }
    }

    // Print all DAA traces that produced 0xA0 or 0xD2
    printf("\n=== DAA operations producing 0xA0 or 0xD2 ===\n");
    for (const auto& t : daa_traces) {
        if (t.a_out == 0xA0 || t.a_out == 0xD2) {
            int n_in = (t.f_in >> 6) & 1;
            int h_in = (t.f_in >> 5) & 1;
            int c_in = (t.f_in >> 4) & 1;
            int z_out = (t.f_out >> 7) & 1;
            int n_out = (t.f_out >> 6) & 1;
            int h_out = (t.f_out >> 5) & 1;
            int c_out = (t.f_out >> 4) & 1;
            printf("PC=%04X: A=%02X F=%02X (N=%d H=%d C=%d) -> A=%02X F=%02X (Z=%d N=%d H=%d C=%d)\n",
                   t.pc, t.a_in, t.f_in, n_in, h_in, c_in,
                   t.a_out, t.f_out, z_out, n_out, h_out, c_out);
        }
    }

    bool passed = serial_output.find("Passed") != std::string::npos;
    printf("\nTest %s\n", passed ? "PASSED" : "FAILED");

    delete[] rom;
    delete sdram;
    delete dut;
    return passed ? 0 : 1;
}
