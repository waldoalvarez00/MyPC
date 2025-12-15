// Run Blargg test with proper serial output capture
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include <cstdio>
#include <cstring>
#include <string>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== Blargg Test Runner with Serial Output ===\n");

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Load ROM
    const char* rom_path = argc > 1 ? argv[1] : "cpu_instrs/individual/01-special.gb";
    FILE* f = fopen(rom_path, "rb");
    if (!f) { printf("Cannot open %s\n", rom_path); return 1; }
    fseek(f, 0, SEEK_END);
    size_t rom_size = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t* rom = new uint8_t[rom_size];
    fread(rom, 1, rom_size, f);
    fclose(f);
    printf("Loaded ROM: %zu bytes\n", rom_size);

    // Load ROM to SDRAM (faster than ioctl download)
    sdram->loadBinary(0, rom, rom_size);

    // Boot ROM with LCD enable and proper register init
    uint8_t boot[256];
    memset(boot, 0, 256);
    int i = 0;
    // SP = 0xFFFE
    boot[i++] = 0x31; boot[i++] = 0xFE; boot[i++] = 0xFF;
    // Enable LCD (LCDC = 0x91)
    boot[i++] = 0x3E; boot[i++] = 0x91;
    boot[i++] = 0xE0; boot[i++] = 0x40;
    // Set registers to post-boot values
    boot[i++] = 0x06; boot[i++] = 0x00;  // B = 0x00
    boot[i++] = 0x0E; boot[i++] = 0x13;  // C = 0x13
    boot[i++] = 0x16; boot[i++] = 0x00;  // D = 0x00
    boot[i++] = 0x1E; boot[i++] = 0xD8;  // E = 0xD8
    boot[i++] = 0x26; boot[i++] = 0x01;  // H = 0x01
    boot[i++] = 0x2E; boot[i++] = 0x4D;  // L = 0x4D
    // A=0x01, F=0xB0 via PUSH DE/POP AF trick
    boot[i++] = 0xD5;                     // PUSH DE (save D,E)
    boot[i++] = 0x16; boot[i++] = 0x01;  // D = 0x01 (will become A)
    boot[i++] = 0x1E; boot[i++] = 0xB0;  // E = 0xB0 (will become F)
    boot[i++] = 0xD5;                     // PUSH DE
    boot[i++] = 0xF1;                     // POP AF (A=0x01, F=0xB0)
    boot[i++] = 0xD1;                     // POP DE (restore D=0x00, E=0xD8)
    // Jump to cartridge
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 100);

    // Upload boot ROM
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

    // Initialize cart_ready (pulse ioctl_wr to trigger cart module)
    printf("Initializing cart_ready...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;  // Cart ROM index
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    // Pulse ioctl_wr to trigger cart_ready
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);
    // Wait for cart_ready
    for (int w = 0; w < 5000 && !dut->dbg_cart_ready; w++) {
        tick_with_sdram(dut, sdram);
    }
    printf("cart_ready = %d\n", dut->dbg_cart_ready);

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    // Serial output capture
    std::string serial_output;
    uint8_t sb_value = 0;           // SB register (0xFF01)
    uint8_t prev_cpu_wr_n = 1;
    int cycles = 0;
    int max_cycles = 2000000000;    // 2B cycles - Some Blargg tests take a very long time
    int last_serial_cycle = 0;
    bool test_complete = false;

    printf("Running test (capturing serial output)...\n\n");
    printf("Serial output:\n");
    printf("----------------------------------------\n");

    int write_count = 0;
    int ff_write_count = 0;

    while (cycles < max_cycles && !test_complete) {
        // Run 1 cycle at a time to catch writes
        tick_with_sdram(dut, sdram);
        cycles++;

        // Detect write (falling edge of wr_n while MREQ active)
        bool cpu_write = (prev_cpu_wr_n == 1 && dut->dbg_cpu_wr_n == 0 && dut->dbg_cpu_mreq_n == 0);

        if (cpu_write) {
            uint16_t addr = dut->dbg_cpu_addr;
            uint8_t data = dut->dbg_cpu_do;
            write_count++;

            // Track writes to 0xFFxx region (quiet)
            if ((addr & 0xFF00) == 0xFF00) {
                ff_write_count++;
            }

            // SB (serial buffer) write at 0xFF01
            if (addr == 0xFF01) {
                sb_value = data;
            }
            // SC (serial control) write at 0xFF02
            else if (addr == 0xFF02) {
                // Bit 7 = transfer start, Bit 0 = internal clock
                if (data & 0x80) {
                    // Transfer initiated - output the SB byte
                    if (sb_value >= 0x20 && sb_value < 0x7F) {
                        putchar(sb_value);
                        fflush(stdout);
                    } else if (sb_value == '\n') {
                        putchar('\n');
                        fflush(stdout);
                    }
                    serial_output += (char)sb_value;
                    last_serial_cycle = cycles;

                    // Check for test completion markers
                    if (serial_output.find("Passed") != std::string::npos ||
                        serial_output.find("Failed") != std::string::npos) {
                        // Let it output a bit more
                        if (cycles - last_serial_cycle > 1000000) {
                            test_complete = true;
                        }
                    }
                }
            }
        }

        prev_cpu_wr_n = dut->dbg_cpu_wr_n;

        // Track intcycle_n transitions for debug
        static uint8_t prev_intcycle_n = 1;
        static uint8_t prev_iff1_dbg = 0;
        if (prev_intcycle_n != dut->dbg_intcycle_n) {
            printf("[%luM] INTCYCLE_n changed: %d -> %d at PC=0x%04X, IF=0x%02X, irq_ack=%d, old_ack_pos=%d\n",
                   (unsigned long)(cycles/1000000), prev_intcycle_n, dut->dbg_intcycle_n,
                   dut->dbg_cpu_pc, dut->dbg_if_r, dut->dbg_irq_ack, dut->dbg_old_ack_pos);
        }
        if (prev_iff1_dbg != dut->dbg_cpu_iff1) {
            printf("[%luM] IFF1 changed: %d -> %d at PC=0x%04X, IF=0x%02X, intcycle_n=%d, irq_ack=%d\n",
                   (unsigned long)(cycles/1000000), prev_iff1_dbg, dut->dbg_cpu_iff1,
                   dut->dbg_cpu_pc, dut->dbg_if_r, dut->dbg_intcycle_n, dut->dbg_irq_ack);
        }
        prev_intcycle_n = dut->dbg_intcycle_n;
        prev_iff1_dbg = dut->dbg_cpu_iff1;

        // Progress report every 5M cycles - include opcode info and timer/interrupt state
        if (cycles % 5000000 == 0) {
            printf("\n[%dM cycles, PC=0x%04X, IR=0x%02X, A=0x%02X, F=0x%02X, LY=%d, writes=%d]\n",
                   cycles/1000000, dut->dbg_cpu_pc, dut->dbg_cpu_ir,
                   dut->dbg_cpu_acc, dut->dbg_cpu_f, dut->dbg_video_ly, write_count);
            printf("  Timer: DIV=0x%02X TIMA=0x%02X TAC=0x%02X irq=%d\n",
                   dut->dbg_timer_div, dut->dbg_timer_tima, dut->dbg_timer_tac, dut->dbg_timer_irq);
            printf("  Int: IE=0x%02X IF=0x%02X IRQ_n=%d HALT=%d IFF1=%d irq_ack=%d intcycle_n=%d\n",
                   dut->dbg_ie_r, dut->dbg_if_r, dut->dbg_irq_n, dut->dbg_cpu_halt, dut->dbg_cpu_iff1,
                   dut->dbg_irq_ack, dut->dbg_intcycle_n);
            printf("  Regs: BC=0x%04X DE=0x%04X HL=0x%04X SP=0x%04X\n",
                   dut->dbg_cpu_bc, dut->dbg_cpu_de, dut->dbg_cpu_hl, dut->dbg_cpu_sp);
            // Detailed JR debug at stuck address
            if (dut->dbg_cpu_pc == 0xC006) {
                printf("  JR Debug: mcycle=0x%02X tstate=0x%02X mcycles=%d mcycles_d=%d JumpE=%d Inc_PC=%d\n",
                       dut->dbg_cpu_mcycle, dut->dbg_cpu_tstate, dut->dbg_cpu_mcycles, dut->dbg_cpu_mcycles_d,
                       dut->dbg_cpu_jump_e, dut->dbg_cpu_inc_pc);
            }
        }

        // One-time detailed trace at PC=0xC006-0xC008 (disabled)
        // static bool traced_c006 = false;
        // static int trace_c006_count = 0;
        // if (!traced_c006 && dut->dbg_cpu_pc >= 0xC004 && dut->dbg_cpu_pc <= 0xC010) {
        //     if (trace_c006_count < 800) {
        //         printf("[PC %04X] IR=%02X mcycle=%02X tstate=%02X mcycles=%d mcycles_d=%d JumpE=%d F=%02X DI=%02X\n",
        //                dut->dbg_cpu_pc, dut->dbg_cpu_ir,
        //                dut->dbg_cpu_mcycle, dut->dbg_cpu_tstate,
        //                dut->dbg_cpu_mcycles, dut->dbg_cpu_mcycles_d,
        //                dut->dbg_cpu_jump_e, dut->dbg_cpu_f,
        //                dut->dbg_cpu_di);
        //         trace_c006_count++;
        //     } else {
        //         traced_c006 = true;
        //     }
        // }

        // (Detailed read trace disabled)

        // (Debug output disabled for serial capture run)

        // Check if test has been idle for a while after outputting "Passed" or "Failed"
        // Give plenty of time for test completion - only stop early if we see the result
        if (serial_output.find("Passed") != std::string::npos ||
            serial_output.find("Failed") != std::string::npos) {
            if ((cycles - last_serial_cycle) > 1000000) {
                printf("\n[Test result found, stopping]\n");
                test_complete = true;
            }
        }
    }

    printf("\n----------------------------------------\n");
    printf("\nWrite statistics: total=%d, 0xFFxx=%d\n", write_count, ff_write_count);
    printf("Serial output complete (%zu bytes):\n", serial_output.size());
    for (char c : serial_output) {
        if (c >= 0x20 && c < 0x7F) putchar(c);
        else if (c == '\n') putchar('\n');
        else printf("[%02X]", (unsigned char)c);
    }
    printf("\n\n");

    // Check result
    bool passed = serial_output.find("Passed") != std::string::npos;
    bool failed = serial_output.find("Failed") != std::string::npos;

    if (passed) {
        printf("TEST PASSED!\n");
    } else if (failed) {
        printf("TEST FAILED!\n");
    } else if (serial_output.empty()) {
        printf("NO SERIAL OUTPUT - test may not have run correctly\n");
    } else {
        printf("Test status unclear - serial output captured but no Pass/Fail marker\n");
    }

    printf("\nFinal state: PC=0x%04X, A=0x%02X, Cycles=%d\n",
           dut->dbg_cpu_pc, dut->dbg_cpu_acc, cycles);

    delete[] rom;
    delete sdram;
    delete dut;
    return passed ? 0 : 1;
}
