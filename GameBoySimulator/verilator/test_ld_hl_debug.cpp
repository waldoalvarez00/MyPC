// Detailed debug test for LD HL,nn instruction timing
// Traces internal signals to understand why H register write is delayed

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

static void upload_boot_rom(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* boot, size_t boot_size) {
    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < (int)boot_size; addr += 2) {
        uint16_t w = boot[addr];
        if (addr + 1 < (int)boot_size) w |= (uint16_t)boot[addr + 1] << 8;
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
}

static void init_cart_ready(Vtop* dut, MisterSDRAMModel* sdram) {
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
    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 5000, sdram);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    printf("=== LD HL,nn Detailed Debug Test ===\n\n");

    // ROM layout at 0x0100:
    //   0x0100: LD HL, $1234  (21 34 12) - L=$34, H=$12
    //   0x0103: NOP           (00)
    //   0x0104: JP $0104      (C3 04 01) - infinite loop
    std::vector<uint8_t> rom(32768, 0x00);
    int i = 0x0100;
    rom[i++] = 0x21; rom[i++] = 0x34; rom[i++] = 0x12;  // LD HL, $1234
    rom[i++] = 0x00;                                      // NOP
    rom[i++] = 0xC3; rom[i++] = 0x04; rom[i++] = 0x01;  // JP $0104

    // Boot ROM: Jump to 0x0100
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    boot[0] = 0xC3; boot[1] = 0x00; boot[2] = 0x01;  // JP $0100

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;

    // Setup VCD trace
    VerilatedVcdC* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);
    tfp->open("ld_hl_debug.vcd");

    sdram->loadBinary(0, rom.data(), rom.size());

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, sdram, 200);

    upload_boot_rom(dut, sdram, boot, sizeof(boot));
    init_cart_ready(dut, sdram);

    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("Running simulation with VCD trace...\n\n");

    // Decode mcycle one-hot
    auto decode_mcycle = [](uint8_t mc) -> int {
        for (int i = 0; i < 7; i++) if (mc & (1 << i)) return i + 1;
        return 0;
    };

    // Decode tstate one-hot
    auto decode_tstate = [](uint8_t ts) -> int {
        for (int i = 0; i < 7; i++) if (ts & (1 << i)) return i + 1;
        return 0;
    };

    printf("Cyc  | PC   | MCyc| TSt | IR   | HL   | di   | Read_To_Reg | Set_BusA_To | Notes\n");
    printf("-----|------|-----|-----|------|------|------|-------------|-------------|------\n");

    bool found_ld = false;
    bool reached_nop = false;
    int ld_start_cycle = 0;
    uint64_t sim_time = 0;

    for (int cycle = 0; cycle < 100000 && !reached_nop; cycle++) {
        tick_with_sdram(dut, sdram);
        tfp->dump(sim_time++);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t ir = dut->dbg_cpu_ir;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;
        uint8_t di = dut->dbg_cpu_di;

        int mc = decode_mcycle(mcycle);
        int ts = decode_tstate(tstate);

        // Track when we enter LD HL instruction
        if (!found_ld && pc == 0x0100 && ir == 0xC3) {
            // Still in JP $0100
        } else if (!found_ld && ir == 0x21) {
            found_ld = true;
            ld_start_cycle = cycle;
        }

        // Log every cycle once we found LD HL until we hit NOP
        if (found_ld && !reached_nop) {
            const char* note = "";
            if (ir == 0x21) {
                if (mc == 1) note = "M1: fetch opcode";
                else if (mc == 2) note = "M2: fetch low byte";
                else if (mc == 3) note = "M3: fetch high byte";
            } else if (ir == 0x00) {
                note = "NOP";
                reached_nop = true;
            }

            // We can't easily access Read_To_Reg and Set_BusA_To from the test harness
            // but we can observe the effects
            printf("%4d | %04X | M%d  | T%d  | 0x%02X | %04X | 0x%02X |     -       |      -      | %s\n",
                cycle - ld_start_cycle, pc, mc, ts, ir, hl, di, note);
        }
    }

    tfp->close();
    printf("\nVCD trace written to ld_hl_debug.vcd\n");

    // Final check
    uint16_t final_hl = dut->dbg_cpu_hl;
    printf("\n=== Final State ===\n");
    printf("HL: 0x%04X (expected 0x1234)\n", final_hl);

    bool pass = (final_hl == 0x1234);
    printf("\n%s\n", pass ? "*** PASS ***" : "*** FAIL ***");

    delete tfp;
    delete dut;
    delete sdram;

    return pass ? 0 : 1;
}
