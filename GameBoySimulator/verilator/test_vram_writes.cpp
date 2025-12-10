// VRAM Write Verification Test
// Purpose: Check if VRAM writes from CPU are actually reaching VRAM
//
// This test monitors the CPU bus during VRAM writes and verifies
// that the data is accessible later

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

void createVRAMTestBootROM(uint8_t* boot_rom) {
    memset(boot_rom, 0, 256);
    int pc = 0;

    // 1. Turn off LCD (required for VRAM access)
    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0xE0;  // LDH ($FF40), A
    boot_rom[pc++] = 0x40;

    // 2. Write distinctive pattern to VRAM $8000-$8003
    boot_rom[pc++] = 0x21;  // LD HL, $8000
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x80;

    boot_rom[pc++] = 0x3E;  // LD A, $AA
    boot_rom[pc++] = 0xAA;
    boot_rom[pc++] = 0x22;  // LD (HL+), A  ; Write $AA to $8000

    boot_rom[pc++] = 0x3E;  // LD A, $55
    boot_rom[pc++] = 0x55;
    boot_rom[pc++] = 0x22;  // LD (HL+), A  ; Write $55 to $8001

    boot_rom[pc++] = 0x3E;  // LD A, $FF
    boot_rom[pc++] = 0xFF;
    boot_rom[pc++] = 0x22;  // LD (HL+), A  ; Write $FF to $8002

    boot_rom[pc++] = 0x3E;  // LD A, $00
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x22;  // LD (HL+), A  ; Write $00 to $8003

    // 3. Read back and verify (read to register B)
    boot_rom[pc++] = 0x21;  // LD HL, $8000
    boot_rom[pc++] = 0x00;
    boot_rom[pc++] = 0x80;

    boot_rom[pc++] = 0x46;  // LD B, (HL)  ; Read $8000 into B (should be $AA)
    boot_rom[pc++] = 0x23;  // INC HL
    boot_rom[pc++] = 0x4E;  // LD C, (HL)  ; Read $8001 into C (should be $55)

    // 4. Infinite loop
    int halt = pc;
    boot_rom[pc++] = 0x18;
    boot_rom[pc++] = (uint8_t)(halt - (pc + 1) - 1);

    printf("  VRAM test boot ROM: %d bytes\n", pc);
}

void downloadBootROM(Vtop* dut, MisterSDRAMModel* sdram, const uint8_t* boot_data, size_t size) {
    dut->boot_download = 1;
    tick_with_sdram(dut, sdram);

    for (size_t addr = 0; addr < size; addr += 2) {
        uint16_t word = boot_data[addr];
        if (addr + 1 < size) {
            word |= (boot_data[addr + 1] << 8);
        }

        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }

        dut->boot_wr = 0;

        for (int i = 0; i < 8; i++) {
            tick_with_sdram(dut, sdram);
        }
    }

    dut->boot_download = 0;

    for (int i = 0; i < 200; i++) {
        tick_with_sdram(dut, sdram);
    }
}

void loadMinimalCart(Vtop* dut, MisterSDRAMModel* sdram) {
    uint8_t cart[0x150];
    memset(cart, 0, sizeof(cart));

    cart[0x100] = 0x18;
    cart[0x101] = 0xFE;

    const uint8_t logo[] = {
        0xCE,0xED,0x66,0x66,0xCC,0x0D,0x00,0x0B,0x03,0x73,0x00,0x83,0x00,0x0C,0x00,0x0D,
        0x00,0x08,0x11,0x1F,0x88,0x89,0x00,0x0E,0xDC,0xCC,0x6E,0xE6,0xDD,0xDD,0xD9,0x99,
        0xBB,0xBB,0x67,0x63,0x6E,0x0E,0xEC,0xCC,0xDD,0xDC,0x99,0x9F,0xBB,0xB9,0x33,0x3E
    };
    memcpy(&cart[0x104], logo, sizeof(logo));

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    tick_with_sdram(dut, sdram);

    for (size_t i = 0; i < sizeof(cart); i++) {
        dut->ioctl_addr = i;
        dut->ioctl_dout = cart[i];
        dut->ioctl_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->ioctl_wr = 0;
    }

    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 10);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    printf("=== VRAM Write Verification Test ===\n\n");

    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel();

    reset_dut_with_sdram(dut, sdram, 100);

    uint8_t boot_rom[256];
    createVRAMTestBootROM(boot_rom);
    downloadBootROM(dut, sdram, boot_rom, 256);

    loadMinimalCart(dut, sdram);

    printf("\n=== Running Boot ROM ===\n");

    // Track CPU state
    uint8_t last_ce_cpu = 0;
    int writes_to_vram = 0;
    uint16_t last_cpu_addr = 0;

    // Run for enough cycles for boot ROM to execute
    for (uint64_t cycle = 0; cycle < 500000; cycle++) {
        tick_with_sdram(dut, sdram);

        // Monitor CPU write operations
        if (dut->dbg_ce_cpu && !last_ce_cpu) {
            uint16_t addr = dut->dbg_cpu_addr;

            // Check for writes to VRAM range ($8000-$9FFF)
            if (addr >= 0x8000 && addr <= 0x9FFF) {
                if (addr != last_cpu_addr) {
                    writes_to_vram++;
                    if (writes_to_vram <= 10) {
                        printf("  [%lu] CPU accessing VRAM addr 0x%04X\n", cycle, addr);
                    }
                    last_cpu_addr = addr;
                }
            }
        }

        last_ce_cpu = dut->dbg_ce_cpu;
    }

    printf("\n=== Results ===\n");
    printf("Total VRAM accesses detected: %d\n", writes_to_vram);

    if (writes_to_vram == 0) {
        printf("❌ NO VRAM WRITES - Boot ROM may not be executing properly\n");
    } else if (writes_to_vram < 4) {
        printf("⚠️  Few VRAM writes (%d) - Expected at least 4\n", writes_to_vram);
    } else {
        printf("✅ VRAM writes detected (%d)\n", writes_to_vram);
    }

    printf("\nNote: This test cannot directly verify if VRAM data persists\n");
    printf("because we don't have direct VRAM read access from the testbench.\n");
    printf("The LCD controller would need to read back the data to verify.\n");

    delete sdram;
    delete dut;

    return 0;
}
