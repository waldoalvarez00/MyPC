// Detailed debug test for INC E instruction
// Traces internal CPU signals at each T-state
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

// Load a file into memory
static bool load_file(const char* path, std::vector<uint8_t>& out) {
    FILE* f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "Failed to open: %s\n", path);
        return false;
    }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz <= 0) {
        fclose(f);
        return false;
    }
    out.resize((size_t)sz);
    const size_t n = fread(out.data(), 1, (size_t)sz, f);
    fclose(f);
    return n == (size_t)sz;
}

// Upload boot ROM
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

// Initialize cart ready signal
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

    // Paths
    const char* rom_path = "test_roms/cpu_instrs/individual/01-special.gb";
    const char* boot_path = "dmg_boot.bin";

    printf("=== INC E Detailed Debug Test ===\n\n");

    // Load ROM
    std::vector<uint8_t> rom;
    if (!load_file(rom_path, rom)) {
        fprintf(stderr, "Failed to load ROM: %s\n", rom_path);
        return 1;
    }
    printf("Loaded ROM: %zu bytes\n", rom.size());

    // Load boot ROM (or create minimal one)
    std::vector<uint8_t> boot;
    if (!load_file(boot_path, boot) && !load_file("../dmg_boot.bin", boot)) {
        fprintf(stderr, "Warning: Boot ROM not found, creating minimal boot ROM\n");
        boot.resize(256);
        memset(boot.data(), 0x00, 256);
        boot[0x000] = 0xC3;  // JP 0x0100
        boot[0x001] = 0x00;
        boot[0x002] = 0x01;
    } else {
        printf("Loaded boot ROM: %zu bytes\n", boot.size());
    }

    // Create DUT and SDRAM model
    Vtop* dut = new Vtop;
    MisterSDRAMModel sdram(8, INTERFACE_NATIVE_SDRAM);
    sdram.cas_latency = 2;
    sdram.debug = false;

    // Load ROM to SDRAM
    printf("Loading cart ROM to SDRAM...\n");
    sdram.loadBinary(0, rom.data(), rom.size());

    // Reset and initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->ioctl_wr = 0;
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_index = 0;
    dut->boot_download = 0;
    dut->boot_wr = 0;
    dut->boot_addr = 0;
    dut->boot_data = 0;
    dut->sd_data_in = 0;
    run_cycles_with_sdram(dut, &sdram, 200);
    dut->reset = 0;

    // Upload boot ROM if available
    if (!boot.empty()) {
        upload_boot_rom(dut, &sdram, boot.data(), boot.size());
    }

    // Initialize cart ready signal
    init_cart_ready(dut, &sdram);

    // Run until we're close to the INC E instruction at PC=0x0208
    printf("Running until PC=0x0206...\n");

    int detailed_log_started = 0;
    int detailed_log_cycles = 0;
    uint8_t prev_tstate = 0;
    uint16_t prev_pc = 0;

    for (int i = 0; i < 2000000; i++) {
        run_cycles_with_sdram(dut, &sdram, 1);

        uint16_t pc = dut->dbg_cpu_pc;
        uint8_t mcycle = dut->dbg_cpu_mcycle;
        uint8_t tstate = dut->dbg_cpu_tstate;

        // Start detailed logging around PC=0x0206
        if (pc == 0x0206 && mcycle == 1 && tstate == 2 && !detailed_log_started) {
            printf("\n=== Starting detailed logging at PC=0x0206 ===\n");
            detailed_log_started = 1;
        }

        // Only log when state changes
        if (detailed_log_started && detailed_log_cycles < 200 && (tstate != prev_tstate || pc != prev_pc)) {
            detailed_log_cycles++;
            prev_tstate = tstate;
            prev_pc = pc;

            // Access debug signals
            uint8_t IR = dut->dbg_cpu_ir;
            uint8_t BusA = dut->dbg_cpu_busa;
            uint8_t BusB = dut->dbg_cpu_busb;
            uint8_t Set_BusA_To = dut->dbg_cpu_set_busa_to;
            uint8_t Set_BusB_To = dut->dbg_cpu_set_busb_to;
            uint8_t RegAddrA = dut->dbg_cpu_regaddra;
            uint8_t Save_ALU_r = dut->dbg_cpu_save_alu_r;
            uint8_t DI_Reg = dut->dbg_cpu_di_latched;

            // Register values
            uint16_t de = dut->dbg_cpu_de;
            uint8_t d_reg = (de >> 8) & 0xFF;
            uint8_t e_reg = de & 0xFF;

            // Decode M-cycle and T-state
            int m = (mcycle & 1) ? 1 : (mcycle & 2) ? 2 : (mcycle & 4) ? 3 : 0;
            int t = (tstate & 2) ? 1 : (tstate & 4) ? 2 : (tstate & 8) ? 3 : (tstate & 16) ? 4 : 0;

            printf("PC=%04X M%d T%d IR=%02X  BusA=%02X BusB=%02X  "
                   "SetBusA=%X RegAddrA=%d Save_ALU_r=%d "
                   "DI=%02X  D=%02X E=%02X\n",
                   pc, m, t,
                   IR, BusA, BusB, Set_BusA_To, RegAddrA,
                   Save_ALU_r, DI_Reg, d_reg, e_reg);

            // Stop after we've seen the result
            if (pc == 0x0209 && m == 1 && t == 2) {
                printf("\n=== After INC E, E is now 0x%02X ===\n", e_reg);
                if (e_reg == 0x01) {
                    printf("SUCCESS: E = 0x01 (correct)\n");
                } else {
                    printf("FAILURE: E = 0x%02X (expected 0x01, got 0x%02X + 1 = 0x%02X)\n",
                           e_reg, e_reg - 1, e_reg);
                    printf("If E=0x1D, then BusA was 0x1C (the INC E opcode)\n");
                }
                break;
            }
        }
    }

    delete dut;
    return 0;
}
