#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

// Helper to decode MCycle bits
const char* decode_mcycle(uint8_t mcycle) {
    if (mcycle == 0x01) return "M1";
    if (mcycle == 0x02) return "M2";
    if (mcycle == 0x04) return "M3";
    if (mcycle == 0x08) return "M4";
    if (mcycle == 0x10) return "M5";
    if (mcycle == 0x20) return "M6";
    if (mcycle == 0x40) return "M7";
    return "??";
}

// Helper to decode TState bits
const char* decode_tstate(uint8_t tstate) {
    if (tstate == 0x01) return "T1";
    if (tstate == 0x02) return "T2";
    if (tstate == 0x04) return "T3";
    if (tstate == 0x08) return "T4";
    if (tstate == 0x10) return "T5";
    if (tstate == 0x20) return "T6";
    if (tstate == 0x40) return "T7";
    return "??";
}

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== JR Instruction MCycle Analysis ===\n\n");
    printf("This test tracks machine cycle (MCycle) and T-state progression\n");
    printf("to identify where JR instruction execution fails.\n\n");

    // Minimal boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;  // DI
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;  // NOP
    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A
    minimal_boot[pc++] = 0x50;

    // Test ROM
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // Fill with HALT

    // At 0x100: JP to 0x150
    rom[0x100] = 0xC3;  // JP $0150
    rom[0x101] = 0x50;
    rom[0x102] = 0x01;

    // At 0x150: JP to 0x160 (working instruction)
    rom[0x150] = 0xC3;  // JP $0160
    rom[0x151] = 0x60;
    rom[0x152] = 0x01;

    // At 0x160: JR +2 (failing instruction)
    rom[0x160] = 0x18;  // JR +2
    rom[0x161] = 0x02;  // Offset
    rom[0x162] = 0x76;  // HALT (should skip)
    rom[0x163] = 0x00;  // NOP (target)

    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    // Upload boot ROM
    printf("Uploading boot ROM...\n");
    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t word = minimal_boot[addr];
        if (addr + 1 < 256) word |= (minimal_boot[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;

    // Simulate cart download
    printf("Simulating cart download...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    for (int i = 0; i < 10; i++) {
        dut->ioctl_addr = i;
        dut->ioctl_wr = 1;
        run_cycles_with_sdram(dut, sdram, 64);
        dut->ioctl_wr = 0;
        run_cycles_with_sdram(dut, sdram, 64);
        if (dut->dbg_cart_ready) break;
    }
    dut->ioctl_download = 0;
    printf("Ready\n\n");

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;
    uint8_t last_ir = 0xFF;
    bool tracing_jp = false;
    bool tracing_jr = false;
    int trace_cycles = 0;

    printf("Running simulation...\n\n");

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot completed at cycle %d\n\n", cycle);
        }

        // Start tracing JP at 0x150
        if (boot_completed && pc == 0x150 && !tracing_jp && !tracing_jr) {
            tracing_jp = true;
            trace_cycles = 0;
            printf("=== JP Instruction at $0150 (opcode=0xC3) ===\n");
            printf("Cycle   PC     IR    MCycle TState MCycles_total  cpu_clken ce_cpu\n");
            printf("-----   ----   ----  ------ ------ -------------  --------- ------\n");
        }

        // Start tracing JR at 0x160
        if (boot_completed && pc == 0x160 && !tracing_jr) {
            tracing_jp = false;  // Stop JP trace
            tracing_jr = true;
            trace_cycles = 0;
            printf("\n");
            printf("=== JR Instruction at $0160 (opcode=0x18) ===\n");
            printf("Cycle   PC     IR    MCycle TState MCycles_total  cpu_clken ce_cpu\n");
            printf("-----   ----   ----  ------ ------ -------------  --------- ------\n");
        }

        // Print trace data when tracing
        if ((tracing_jp || tracing_jr) && trace_cycles < 400) {
            if (trace_cycles % 4 == 0) {  // Print every 4 cycles to keep output manageable
                printf("%5d  $%04X   $%02X   %s     %s        %d          %d         %d\n",
                       cycle, pc, ir,
                       decode_mcycle(dut->dbg_cpu_mcycle),
                       decode_tstate(dut->dbg_cpu_tstate),
                       dut->dbg_cpu_mcycles,
                       dut->dbg_cpu_clken,
                       dut->dbg_ce_cpu);
            }
            trace_cycles++;

            // Stop JP trace after PC advances beyond 0x15F
            if (tracing_jp && pc >= 0x160) {
                tracing_jp = false;
                printf("\n>>> JP completed: PC jumped to $0160 ✅\n");
            }

            // Success if JR reaches 0x163
            if (tracing_jr && pc == 0x163) {
                printf("\n>>> JR SUCCESS: PC jumped to $0163 ✅\n\n");
                break;
            }

            // Only declare failure if we're in M1 (next instruction) with wrong PC
            // Don't break during M3 as jump happens at T3
            if (tracing_jr && pc == 0x162 && dut->dbg_cpu_mcycle == 0x01) {
                printf("\n>>> JR FAILED: Started next instruction at $0162 (HALT) instead of jumping to $0163 ❌\n");
                printf("    Expected: $0160 → $0163 (relative jump)\n");
                printf("    Actual:   Started fetching instruction at $0162\n\n");
                break;
            }

            // Safety: stop tracing after 400 cycles
            if (trace_cycles >= 400) {
                if (tracing_jp) {
                    printf("\n(JP trace stopped after 400 cycles)\n");
                    tracing_jp = false;
                }
                if (tracing_jr) {
                    printf("\n(JR trace stopped after 400 cycles - PC stuck at $%04X)\n", pc);
                    break;
                }
            }
        }

        // Update tracking
        if (pc != last_pc) {
            last_pc = pc;
        }
        if (ir != last_ir) {
            last_ir = ir;
        }
    }

    printf("\n=== Analysis ===\n\n");
    printf("Expected JR execution:\n");
    printf("  MCycle[0] (M1): Fetch opcode 0x18 from $0160\n");
    printf("  MCycle[1] (M2): Fetch offset byte from $0161, Inc_PC asserted\n");
    printf("  MCycle[2] (M3): JumpE asserted, PC = PC + sign_extended_offset\n");
    printf("                  PC should become $0163 (0x0161 + 2)\n\n");

    printf("If JR failed:\n");
    printf("  - Check if MCycle reached M3 (MCycle[2])\n");
    printf("  - Check if MCycles_total was set to 3\n");
    printf("  - Look for premature instruction completion\n\n");

    printf("Next steps:\n");
    printf("  1. Compare JP vs JR MCycle progression\n");
    printf("  2. Verify MCycles_total is 3 for JR (should match microcode)\n");
    printf("  3. Check if M3 cycle executes for JR\n\n");

    delete sdram;
    delete dut;

    return (last_pc == 0x162) ? 1 : 0;  // Return error if hit HALT
}
