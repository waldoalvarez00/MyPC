#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

// Cycle-by-cycle trace structure
struct CycleTrace {
    int cycle;
    uint16_t pc;
    uint8_t data;
    bool cpu_clken;
    bool ce_cpu;
    bool cart_rd;
    bool cpu_rd_n;
    bool cpu_mreq_n;
    bool boot_enabled;
};

void print_trace(const char* title, CycleTrace* traces, int count) {
    printf("\n=== %s ===\n", title);
    printf("Cycle   PC     Data  cpu_clken ce_cpu cart_rd cpu_rd_n cpu_mreq_n boot_en\n");
    printf("-----   ----   ----  --------- ------ ------- -------- ---------- -------\n");
    for (int i = 0; i < count; i++) {
        CycleTrace& t = traces[i];
        printf("%5d  $%04X   $%02X      %d        %d       %d        %d         %d         %d\n",
               t.cycle, t.pc, t.data, t.cpu_clken, t.ce_cpu, t.cart_rd,
               t.cpu_rd_n, t.cpu_mreq_n, t.boot_enabled);
    }
}

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic latency

    printf("=== JR Instruction Cycle-by-Cycle Trace ===\n\n");
    printf("This test compares JP (working) vs JR (failing) cycle-by-cycle\n");
    printf("to identify why cpu_clken becomes 0 during JR execution.\n\n");

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

    // At 0x150: JP to 0x160 (working instruction for comparison)
    rom[0x150] = 0xC3;  // JP $0160
    rom[0x151] = 0x60;
    rom[0x152] = 0x01;

    // At 0x160: JR +2 (failing instruction)
    rom[0x160] = 0x18;  // JR +2
    rom[0x161] = 0x02;  // Offset
    rom[0x162] = 0x76;  // HALT (should skip)
    rom[0x163] = 0x00;  // NOP (target)
    rom[0x164] = 0x76;  // HALT

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

    // Trace arrays
    CycleTrace jp_trace[200];  // Trace for JP at 0x150
    CycleTrace jr_trace[200];  // Trace for JR at 0x160
    int jp_count = 0;
    int jr_count = 0;

    bool boot_completed = false;
    bool tracing_jp = false;
    bool tracing_jr = false;
    uint16_t last_pc = 0xFFFF;
    int global_cycle = 0;

    printf("Running simulation...\n");

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);
        global_cycle++;

        uint16_t pc = dut->dbg_cpu_addr;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Detect boot completion
        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
            printf("Boot completed at cycle %d\n", cycle);
        }

        // Start tracing when we reach JP at 0x150
        if (boot_completed && pc == 0x150 && !tracing_jp) {
            tracing_jp = true;
            printf("Started tracing JP instruction at 0x150 (cycle %d)\n", cycle);
        }

        // Start tracing when we reach JR at 0x160
        if (boot_completed && pc == 0x160 && !tracing_jr) {
            tracing_jr = true;
            printf("Started tracing JR instruction at 0x160 (cycle %d)\n", cycle);
        }

        // Capture JP trace (0x150-0x15F, 100 cycles)
        if (tracing_jp && pc >= 0x150 && pc < 0x160 && jp_count < 100) {
            CycleTrace& t = jp_trace[jp_count++];
            t.cycle = global_cycle;
            t.pc = pc;
            t.data = (pc < sizeof(rom)) ? rom[pc] : 0xFF;
            t.cpu_clken = dut->dbg_cpu_clken;
            t.ce_cpu = dut->dbg_ce_cpu;
            t.cart_rd = dut->dbg_cart_rd;
            t.cpu_rd_n = dut->dbg_cpu_rd_n;
            t.cpu_mreq_n = 0;  // Not available as debug signal
            t.boot_enabled = boot_enabled;
        }

        // Stop JP tracing after 100 cycles
        if (tracing_jp && jp_count >= 100) {
            tracing_jp = false;
        }

        // Capture JR trace (0x160-0x165, 100 cycles)
        if (tracing_jr && pc >= 0x160 && pc <= 0x165 && jr_count < 100) {
            CycleTrace& t = jr_trace[jr_count++];
            t.cycle = global_cycle;
            t.pc = pc;
            t.data = (pc < sizeof(rom)) ? rom[pc] : 0xFF;
            t.cpu_clken = dut->dbg_cpu_clken;
            t.ce_cpu = dut->dbg_ce_cpu;
            t.cart_rd = dut->dbg_cart_rd;
            t.cpu_rd_n = dut->dbg_cpu_rd_n;
            t.cpu_mreq_n = 0;  // Not available as debug signal
            t.boot_enabled = boot_enabled;
        }

        // Stop JR tracing after 100 cycles or if we hit HALT
        if (tracing_jr && (jr_count >= 100 || pc == 0x162)) {
            tracing_jr = false;
            if (pc == 0x162) {
                printf("JR FAILED: Hit HALT at 0x162 (cycle %d)\n", cycle);
            }
            break;
        }

        // Exit if we successfully reach 0x163
        if (pc == 0x163) {
            printf("JR SUCCESS: Reached target at 0x163 (cycle %d)\n", cycle);
            break;
        }

        last_pc = pc;
    }

    // Print traces
    printf("\n");
    print_trace("JP Instruction Trace (0x150-0x15F) - WORKING", jp_trace, jp_count);
    printf("\n");
    print_trace("JR Instruction Trace (0x160-0x165) - FAILING", jr_trace, jr_count);

    // Analysis
    printf("\n=== Analysis ===\n\n");

    // Count cycles where cpu_clken=0 for each instruction
    int jp_clken_0 = 0, jp_clken_1 = 0;
    int jr_clken_0 = 0, jr_clken_1 = 0;

    for (int i = 0; i < jp_count; i++) {
        if (jp_trace[i].cpu_clken) jp_clken_1++; else jp_clken_0++;
    }

    for (int i = 0; i < jr_count; i++) {
        if (jr_trace[i].cpu_clken) jr_clken_1++; else jr_clken_0++;
    }

    printf("JP Instruction (working):\n");
    printf("  cpu_clken=1: %d cycles (%.1f%%)\n", jp_clken_1, 100.0*jp_clken_1/jp_count);
    printf("  cpu_clken=0: %d cycles (%.1f%%)\n", jp_clken_0, 100.0*jp_clken_0/jp_count);
    printf("\n");

    printf("JR Instruction (failing):\n");
    printf("  cpu_clken=1: %d cycles (%.1f%%)\n", jr_clken_1, 100.0*jr_clken_1/jr_count);
    printf("  cpu_clken=0: %d cycles (%.1f%%)\n", jr_clken_0, 100.0*jr_clken_0/jr_count);
    printf("\n");

    // Compare ce_cpu patterns
    printf("Comparing ce_cpu patterns:\n");
    printf("JP: ");
    for (int i = 0; i < (jp_count < 30 ? jp_count : 30); i++) {
        printf("%d", jp_trace[i].ce_cpu ? 1 : 0);
    }
    printf("\n");
    printf("JR: ");
    for (int i = 0; i < (jr_count < 30 ? jr_count : 30); i++) {
        printf("%d", jr_trace[i].ce_cpu ? 1 : 0);
    }
    printf("\n\n");

    // Find PC changes in each trace
    printf("PC transitions:\n");
    printf("JP: ");
    uint16_t last_jp_pc = 0xFFFF;
    for (int i = 0; i < jp_count; i++) {
        if (jp_trace[i].pc != last_jp_pc) {
            printf("$%04X ", jp_trace[i].pc);
            last_jp_pc = jp_trace[i].pc;
        }
    }
    printf("\n");

    printf("JR: ");
    uint16_t last_jr_pc = 0xFFFF;
    for (int i = 0; i < jr_count; i++) {
        if (jr_trace[i].pc != last_jr_pc) {
            printf("$%04X ", jr_trace[i].pc);
            last_jr_pc = jr_trace[i].pc;
        }
    }
    printf("\n\n");

    printf("Conclusion:\n");
    if (jr_clken_0 > jr_clken_1) {
        printf("  ❌ JR instruction has cpu_clken=0 most of the time\n");
        printf("  ❌ This prevents CPU from executing the jump\n");
        printf("  ❌ Root cause: CPU clock enable logic issue\n");
    } else {
        printf("  ✅ CPU clock enable appears normal\n");
        printf("  ⚠️  Issue may be in CPU core itself\n");
    }

    delete sdram;
    delete dut;

    return (last_jr_pc == 0x162) ? 1 : 0;  // Return error if hit HALT
}
