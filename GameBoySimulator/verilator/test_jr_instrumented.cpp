#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

// Enhanced tick with full instrumentation
void instrumented_tick(Vtop* dut, MisterSDRAMModel* sdram, int cycle, bool trace) {
    static uint16_t last_pc = 0xFFFF;
    static bool last_cart_read = false;

    // Rising edge
    dut->clk_sys = 1;
    dut->eval();

    // Capture signals on rising edge (before SDRAM processes)
    uint16_t pc = dut->dbg_cpu_addr;
    bool cpu_rd_n = dut->dbg_cpu_rd_n;
    bool cpu_wr_n = dut->dbg_cpu_wr_n;
    bool cart_rd = dut->dbg_cart_rd;
    bool cpu_clken = dut->dbg_cpu_clken;
    bool ce_cpu = dut->dbg_ce_cpu;
    bool hdma_active = dut->dbg_hdma_active;
    bool dma_rd = dut->dbg_dma_rd;

    bool cpu_reading = cart_rd;  // Simplified: cart_rd indicates CPU reading from cart

    if (trace) {
        if (pc != last_pc || cpu_reading != last_cart_read) {
            printf("[%6d] PC=$%04X cpu_rd=%d cpu_wr=%d cart_rd=%d cpu_clken=%d ce_cpu=%d\n",
                   cycle, pc, !cpu_rd_n, !cpu_wr_n, cart_rd, cpu_clken, ce_cpu);
            last_pc = pc;
            last_cart_read = cpu_reading;
        }
    }

    // Process SDRAM
    uint16_t rdata = 0;
    bool compl_out = false;
    bool config_done = false;

    sdram->processNativeSDRAM(
        dut->sd_cs,
        dut->sd_ras,
        dut->sd_cas,
        dut->sd_we,
        dut->sd_ba,
        dut->sd_addr,
        dut->sd_data_out,
        dut->sd_dqm,
        rdata,
        compl_out,
        config_done
    );
    dut->sd_data_in = rdata;

    // Falling edge
    dut->clk_sys = 0;
    dut->eval();
}

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    printf("=== JR Instruction Instrumented Debug ===\n\n");

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

    // Test ROM: Side-by-side JP and JR
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));  // Fill with HALT

    // Entry
    rom[0x100] = 0xC3;  // JP $0150
    rom[0x101] = 0x50;
    rom[0x102] = 0x01;

    // Test JP first (known working)
    rom[0x150] = 0xC3;  // JP $0160
    rom[0x151] = 0x60;
    rom[0x152] = 0x01;

    // Test JR
    rom[0x160] = 0x18;  // JR +2
    rom[0x161] = 0x02;  // Offset = +2
    rom[0x162] = 0x76;  // HALT (should skip)
    rom[0x163] = 0x00;  // NOP (target)

    printf("Test Configuration:\n");
    printf("  0x0150: JP $0160 (known working)\n");
    printf("  0x0160: JR +2 → $0163 (testing)\n");
    printf("  0x0162: HALT (should skip)\n");
    printf("  0x0163: NOP (target)\n\n");

    printf("ROM bytes:\n");
    printf("  @0x0150: %02X %02X %02X\n", rom[0x150], rom[0x151], rom[0x152]);
    printf("  @0x0160: %02X %02X %02X %02X\n\n", rom[0x160], rom[0x161], rom[0x162], rom[0x163]);

    // Load into SDRAM
    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    for (int i = 0; i < 50; i++) {
        instrumented_tick(dut, sdram, i, false);
    }
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
        for (int i = 0; i < 4; i++) instrumented_tick(dut, sdram, 50 + addr*8 + i, false);
        dut->boot_wr = 0;
        for (int i = 0; i < 4; i++) instrumented_tick(dut, sdram, 50 + addr*8 + 4 + i, false);
    }
    dut->boot_download = 0;

    // Simulate cart download
    printf("Simulating cart download...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    for (int i = 0; i < 10; i++) {
        dut->ioctl_addr = i;
        dut->ioctl_wr = 1;
        for (int j = 0; j < 64; j++) instrumented_tick(dut, sdram, 3000 + i*128 + j, false);
        dut->ioctl_wr = 0;
        for (int j = 0; j < 64; j++) instrumented_tick(dut, sdram, 3000 + i*128 + 64 + j, false);
        if (dut->dbg_cart_ready) break;
    }
    dut->ioctl_download = 0;

    printf("\n=== Starting Instrumented Trace ===\n\n");

    bool boot_completed = false;
    bool tracing = false;
    bool jp_seen = false;
    bool jr_seen = false;
    int trace_cycles = 0;
    int max_trace_cycles = 500;

    for (int cycle = 5000; cycle < 100000; cycle++) {
        uint16_t pc_before = dut->dbg_cpu_addr;

        instrumented_tick(dut, sdram, cycle, tracing);

        uint16_t pc = dut->dbg_cpu_addr;

        // Detect boot completion
        if (!boot_completed && !dut->dbg_boot_rom_enabled) {
            boot_completed = true;
            printf("Boot ROM completed at cycle %d\n\n", cycle);
        }

        // Start tracing when we reach JP at 0x150
        if (boot_completed && pc == 0x150 && !jp_seen) {
            jp_seen = true;
            tracing = true;
            trace_cycles = 0;
            printf("=== TRACE START: JP at 0x0150 ===\n");
        }

        // Start detailed trace when we reach JR at 0x160
        if (boot_completed && pc == 0x160 && !jr_seen && jp_seen) {
            jr_seen = true;
            trace_cycles = 0;
            printf("\n=== TRACE START: JR at 0x0160 ===\n");
            printf("Expected: PC should go 0x0160 → 0x0161 → 0x0163 (skip 0x0162)\n");
            printf("If bug: PC will go 0x0160 → 0x0161 → 0x0162 (HALT)\n\n");
        }

        if (tracing) {
            trace_cycles++;

            // Show byte fetch
            if (pc != pc_before) {
                uint8_t opcode = (pc >= 0x100 && pc < 0x200) ? rom[pc] : 0xFF;
                printf("  [%6d] PC=$%04X (byte=0x%02X", cycle, pc, opcode);

                if (pc == 0x150) printf(" = JP opcode");
                else if (pc == 0x151) printf(" = JP addr_lo");
                else if (pc == 0x152) printf(" = JP addr_hi");
                else if (pc == 0x160) printf(" = JR opcode ← START TRACKING");
                else if (pc == 0x161) printf(" = JR offset");
                else if (pc == 0x162) printf(" = HALT ← ❌ BUG! Should skip");
                else if (pc == 0x163) printf(" = NOP ← ✅ Correct target");
                else if (pc == 0x164) printf(" = ??? ← Went too far");

                printf(")\n");
            }

            // Stop tracing after JR completes or fails
            if (jr_seen && trace_cycles > max_trace_cycles) {
                printf("\n=== TRACE END (timeout) ===\n");
                break;
            }

            // Stop if we hit HALT at 0x162 (JR failed)
            if (jr_seen && pc == 0x162) {
                printf("\n❌ JR FAILED: Reached HALT at 0x0162!\n");
                printf("   JR did NOT jump from 0x0160\n");
                printf("   PC sequence: 0x0160 → 0x0161 → 0x0162 (wrong!)\n");
                printf("   Expected: 0x0160 → 0x0161 → 0x0163 (skip 0x0162)\n\n");
                break;
            }

            // Stop if we reach target at 0x163 (JR worked)
            if (jr_seen && pc == 0x163) {
                printf("\n✅ JR WORKED: Reached target at 0x0163!\n");
                printf("   JR successfully jumped from 0x0160\n");
                printf("   PC sequence: 0x0160 → 0x0161 → 0x0163 (correct!)\n\n");
                break;
            }
        }
    }

    delete sdram;
    delete dut;

    if (!jr_seen) {
        printf("\n⚠️  Never reached JR instruction at 0x0160\n");
        return 1;
    } else if (dut->dbg_cpu_addr == 0x162) {
        printf("RESULT: JR instruction FAILED ❌\n");
        return 1;
    } else if (dut->dbg_cpu_addr == 0x163) {
        printf("RESULT: JR instruction WORKED ✅\n");
        return 0;
    } else {
        printf("\nRESULT: Test inconclusive (PC=$%04X)\n", dut->dbg_cpu_addr);
        return 1;
    }
}
