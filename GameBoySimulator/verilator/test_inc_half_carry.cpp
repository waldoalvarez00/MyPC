// Test for INC half-carry flag issue
// INC E with E=0x0E should NOT set half-carry (H flag)

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
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
    printf("=== INC Half-Carry Test ===\n\n");

    // Boot ROM: Set up E=0x0E and JP to test code
    uint8_t boot[256];
    memset(boot, 0x00, sizeof(boot));
    int i = 0;
    boot[i++] = 0x1E; boot[i++] = 0x0E;  // LD E, $0E (E=14)
    boot[i++] = 0x37;                     // SCF - Set carry flag  
    boot[i++] = 0xC3; boot[i++] = 0x00; boot[i++] = 0x01;  // JP $0100

    // Cart ROM at 0x0100: INC E then loop
    std::vector<uint8_t> rom(32768, 0x00);
    rom[0x0100] = 0x1C;  // INC E - E goes from 0x0E to 0x0F
    rom[0x0101] = 0x00;  // NOP
    rom[0x0102] = 0xC3; rom[0x0103] = 0x02; rom[0x0104] = 0x01;  // JP $0102 (loop)

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;
    sdram->debug = false;
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

    printf("Running simulation...\n\n");
    printf("Cycle | PC   | E  | F  | Notes\n");
    printf("------|------|----|----|------\n");

    uint16_t prev_pc = 0;
    uint8_t prev_e = 0, prev_f = 0;
    int logged = 0;

    for (int cycle = 0; cycle < 50000 && logged < 30; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_pc;
        uint16_t de = dut->dbg_cpu_de;
        uint8_t e = de & 0xFF;
        uint8_t f = dut->dbg_cpu_f;

        bool changed = (pc != prev_pc) || (e != prev_e) || (f != prev_f);
        
        if (changed && (pc >= 0x0100 || (prev_pc >= 0x0100))) {
            const char* note = "";
            if (pc == 0x0100) note = "INC E start";
            if (pc == 0x0101 && prev_pc == 0x0100) note = "After INC E";
            
            printf("%5d | %04X | %02X | %02X | %s\n", cycle, pc, e, f, note);
            logged++;
        }
        prev_pc = pc;
        prev_e = e;
        prev_f = f;
    }

    // Final check
    uint16_t de = dut->dbg_cpu_de;
    uint8_t e = de & 0xFF;
    uint8_t f = dut->dbg_cpu_f;
    
    printf("\n=== Results ===\n");
    printf("E: 0x%02X (expected 0x0F)\n", e);
    printf("F: 0x%02X (expected 0x10 - Z=0 N=0 H=0 C=1)\n", f);
    printf("\nF breakdown:\n");
    printf("  Z (Zero):       %d\n", (f >> 7) & 1);
    printf("  N (Subtract):   %d\n", (f >> 6) & 1);
    printf("  H (Half-carry): %d (should be 0 for E=0x0E+1=0x0F)\n", (f >> 5) & 1);
    printf("  C (Carry):      %d (should be 1 from SCF)\n", (f >> 4) & 1);

    if (e == 0x0F && f == 0x10) {
        printf("\n*** PASS ***\n");
        return 0;
    } else {
        printf("\n*** FAIL ***\n");
        if ((f >> 5) & 1) {
            printf("    Half-carry flag incorrectly set!\n");
            printf("    INC E from 0x0E to 0x0F should not set H.\n");
        }
        return 1;
    }
}
