#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;

    // Boot ROM
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);
    int pc = 0;
    minimal_boot[pc++] = 0xF3;
    while (pc < 0xFC) minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x3E; minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0; minimal_boot[pc++] = 0x50;

    // Test ROM - Test carry flag setting and JR C/NC
    uint8_t rom[32768];
    memset(rom, 0x76, sizeof(rom));

    rom[0x100] = 0xC3; rom[0x101] = 0x50; rom[0x102] = 0x01;  // JP $0150

    // Test 1: Set carry with SCF, then JR C
    rom[0x150] = 0x37;  // SCF - set carry flag
    rom[0x151] = 0x00;  // NOP (marker)
    rom[0x152] = 0x38; rom[0x153] = 0x02;  // JR C, +2 (should jump to 0x156)
    rom[0x154] = 0x00;  // NOP (should skip)
    rom[0x155] = 0x76;  // HALT (should skip)
    rom[0x156] = 0x00;  // NOP (target if JR C works)
    
    // Test 2: Clear carry with CCF, then JR NC
    rom[0x157] = 0x3F;  // CCF - complement carry (clear it)
    rom[0x158] = 0x00;  // NOP (marker)
    rom[0x159] = 0x30; rom[0x15A] = 0x02;  // JR NC, +2 (should jump to 0x15D)
    rom[0x15B] = 0x00;  // NOP (should skip)
    rom[0x15C] = 0x76;  // HALT (should skip)
    rom[0x15D] = 0x00;  // NOP (target if JR NC works)
    
    // Success marker
    rom[0x15E] = 0x76;  // HALT (success)

    sdram->loadBinary(0, rom, sizeof(rom));

    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

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

    bool boot_completed = false;
    uint16_t last_pc = 0xFFFF;
    bool jr_c_taken = false;
    bool jr_nc_taken = false;
    bool scf_executed = false;
    bool ccf_executed = false;

    printf("Testing carry flag and conditional JR...\n\n");
    printf("Expected sequence:\n");
    printf("  $0150: SCF (set carry)\n");
    printf("  $0151: NOP\n");
    printf("  $0152: JR C, +2 (should jump)\n");
    printf("  $0156: NOP (target) ← Should skip $0154-$0155\n");
    printf("  $0157: CCF (clear carry)\n");
    printf("  $0158: NOP\n");
    printf("  $0159: JR NC, +2 (should jump)\n");
    printf("  $015D: NOP (target) ← Should skip $015B-$015C\n");
    printf("  $015E: HALT (success)\n\n");

    printf("Actual execution:\n");

    for (int cycle = 0; cycle < 200000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint8_t ir = dut->dbg_cpu_ir;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (!boot_completed && !boot_enabled) {
            boot_completed = true;
        }

        if (boot_completed && pc >= 0x150 && pc <= 0x15F && pc != last_pc) {
            printf("  PC = $%04X", pc);
            
            if (pc == 0x150) printf(" (SCF)");
            else if (pc == 0x151) { scf_executed = true; printf(" (NOP after SCF)"); }
            else if (pc == 0x152) printf(" (JR C)");
            else if (pc == 0x153) printf(" (JR C offset)");
            else if (pc == 0x154) printf(" (NOP - should skip!) ❌");
            else if (pc == 0x155) printf(" (HALT - should skip!) ❌");
            else if (pc == 0x156) { jr_c_taken = true; printf(" (NOP - JR C target) ✅"); }
            else if (pc == 0x157) printf(" (CCF)");
            else if (pc == 0x158) { ccf_executed = true; printf(" (NOP after CCF)"); }
            else if (pc == 0x159) printf(" (JR NC)");
            else if (pc == 0x15A) printf(" (JR NC offset)");
            else if (pc == 0x15B) printf(" (NOP - should skip!) ❌");
            else if (pc == 0x15C) printf(" (HALT - should skip!) ❌");
            else if (pc == 0x15D) { jr_nc_taken = true; printf(" (NOP - JR NC target) ✅"); }
            else if (pc == 0x15E) printf(" (HALT - success)");
            
            printf("\n");
            last_pc = pc;
            
            if (pc == 0x15E) {
                break;  // Reached success marker
            }
        }
    }

    printf("\n=== Results ===\n");
    printf("SCF executed: %s\n", scf_executed ? "Yes" : "No");
    printf("JR C taken: %s %s\n", jr_c_taken ? "Yes ✅" : "No ❌", 
           jr_c_taken ? "(correct)" : "(BUG - should have jumped)");
    printf("CCF executed: %s\n", ccf_executed ? "Yes" : "No");
    printf("JR NC taken: %s %s\n", jr_nc_taken ? "Yes ✅" : "No ❌",
           jr_nc_taken ? "(correct)" : "(BUG - should have jumped)");

    if (jr_c_taken && jr_nc_taken) {
        printf("\n🎉 All tests PASSED!\n");
    } else {
        printf("\n❌ Some tests FAILED\n");
    }

    delete sdram;
    delete dut;
    return (jr_c_taken && jr_nc_taken) ? 0 : 1;
}
