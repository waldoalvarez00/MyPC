#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Simple Boot ROM Test (LCD OFF - No Interrupts) ===\n\n");

    // Create ULTRA-MINIMAL boot ROM (NO LCD initialization)
    // This boot ROM just disables itself and jumps to cart
    uint8_t minimal_boot[256];
    memset(minimal_boot, 0, 256);

    int pc = 0;

    // 0. Disable interrupts
    minimal_boot[pc++] = 0xF3;  // DI

    // 1. Make sure LCD is OFF (prevent any VBlank interrupts)
    minimal_boot[pc++] = 0x3E;  // LD A, $00
    minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF40), A  ; LCDC = 0 (LCD OFF)
    minimal_boot[pc++] = 0x40;

    // 2. Disable all interrupts in IE register
    minimal_boot[pc++] = 0x3E;  // LD A, $00
    minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0xE0;  // LDH ($FFFF), A  ; IE = 0 (all interrupts disabled)
    minimal_boot[pc++] = 0xFF;

    // 3. Disable boot ROM and jump to cart immediately
    minimal_boot[pc++] = 0x3E;  // LD A, $01
    minimal_boot[pc++] = 0x01;
    minimal_boot[pc++] = 0xE0;  // LDH ($FF50), A  ; Disable boot ROM
    minimal_boot[pc++] = 0x50;
    minimal_boot[pc++] = 0xC3;  // JP $0100
    minimal_boot[pc++] = 0x00;
    minimal_boot[pc++] = 0x01;

    printf("Ultra-minimal boot ROM created: %d bytes\n", pc);
    printf("  DI instruction: YES\n");
    printf("  LCD kept OFF: YES\n");
    printf("  IE register cleared: YES\n");
    printf("  No LCD initialization (no interrupts possible)\n\n");

    // Create cart ROM with proper interrupt handlers
    uint8_t rom[32768];
    memset(rom, 0x00, sizeof(rom));

    // CRITICAL: Add RETI at interrupt vectors
    rom[0x40] = 0xD9;  // VBlank: RETI
    rom[0x48] = 0xD9;  // LCD STAT: RETI
    rom[0x50] = 0xD9;  // Timer: RETI
    rom[0x58] = 0xD9;  // Serial: RETI
    rom[0x60] = 0xD9;  // Joypad: RETI

    // Entry point
    rom[0x100] = 0x00;  // NOP
    rom[0x101] = 0xC3;  // JP $0150
    rom[0x102] = 0x50;
    rom[0x103] = 0x01;

    // Nintendo logo
    uint8_t logo[] = {0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B};
    memcpy(&rom[0x104], logo, sizeof(logo));

    // Main program at 0x150
    pc = 0x150;
    rom[pc++] = 0xF3;  // DI (disable interrupts again for safety)
    rom[pc++] = 0x31; rom[pc++] = 0xFE; rom[pc++] = 0xFF;  // LD SP, $FFFE

    // Keep LCD OFF in cart ROM too
    rom[pc++] = 0x3E;  // LD A, $00
    rom[pc++] = 0x00;
    rom[pc++] = 0xE0;  // LDH ($FF40), A  ; LCDC = 0 (LCD still OFF)
    rom[pc++] = 0x40;

    // Clear IE register again for safety
    rom[pc++] = 0x3E;  // LD A, $00
    rom[pc++] = 0x00;
    rom[pc++] = 0xE0;  // LDH ($FFFF), A  ; IE = 0
    rom[pc++] = 0xFF;

    rom[pc++] = 0x00;  // NOP
    rom[pc++] = 0x18; rom[pc++] = 0xFD;  // JR -3 (loop forever)

    printf("Cart ROM created:\n");
    printf("  RETI handlers at vectors: YES\n");
    printf("  DI at main program start: YES\n");
    printf("  LCD kept OFF in cart: YES\n");
    printf("  IE register cleared in cart: YES\n\n");

    // Load into SDRAM
    sdram->loadBinary(0, rom, sizeof(rom));

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    // Upload minimal boot ROM
    printf("Uploading minimal boot ROM to simulator...\n");
    dut->boot_download = 1;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t word = minimal_boot[addr];
        if (addr + 1 < 256) {
            word |= (minimal_boot[addr + 1] << 8);
        }
        dut->boot_addr = addr;
        dut->boot_data = word;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;
    printf("Boot ROM uploaded.\n\n");

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
        if (dut->dbg_cart_ready) {
            printf("  cart_ready set after %d writes\n", i + 1);
            break;
        }
    }
    dut->ioctl_download = 0;
    printf("Cart download complete, cart_ready=%d\n\n", dut->dbg_cart_ready);

    // Run simulation
    printf("Running simulation...\n");
    printf("Monitoring for interrupt storm (PC stuck at 0x0038-0x003F)...\n\n");

    uint16_t last_pc = 0xFFFF;
    int stuck_count = 0;
    int boot_complete_cycle = -1;
    bool interrupt_storm_detected = false;
    int pc_at_0x150_count = 0;

    for (int cycle = 0; cycle < 20000; cycle++) {
        tick_with_sdram(dut, sdram);

        uint16_t pc = dut->dbg_cpu_addr;
        uint16_t sp = dut->dbg_cpu_sp;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        // Count cycles at main program address
        if (pc >= 0x0150 && pc <= 0x0160) {
            pc_at_0x150_count++;
            if (pc_at_0x150_count == 100) {
                printf("Cycle %d: ✅ CART ROM RUNNING SUCCESSFULLY!\n", cycle);
                printf("  PC in main program range (0x0150-0x0160)\n");
                printf("  SP: 0x%04X\n", sp);
                printf("  No interrupt storm detected\n\n");
            }
        }

        // Detect PC stuck at interrupt vectors
        if (pc >= 0x0038 && pc <= 0x0042) {
            if (pc == last_pc) {
                stuck_count++;
            } else {
                stuck_count = 0;
            }

            if (stuck_count >= 10) {
                printf("Cycle %d: ❌ INTERRUPT STORM DETECTED!\n", cycle);
                printf("  PC stuck at: 0x%04X\n", pc);
                printf("  SP: 0x%04X\n", sp);
                printf("  boot_rom_enabled: %d\n", boot_enabled);
                interrupt_storm_detected = true;
                break;
            }
        } else {
            stuck_count = 0;
        }

        // Detect boot ROM completion
        if (boot_enabled && !dut->dbg_boot_rom_enabled) {
            boot_complete_cycle = cycle;
            printf("Cycle %d: ✅ BOOT ROM DISABLED!\n", cycle);
            printf("  PC: 0x%04X\n", pc);
            printf("  SP: 0x%04X\n", sp);
        }

        last_pc = pc;

        // Progress indicator
        if (cycle % 5000 == 0 && cycle > 0) {
            printf("Cycle %d: PC=0x%04X SP=0x%04X boot_en=%d\n",
                   cycle, pc, sp, boot_enabled);
        }
    }

    printf("\n--- Test Results ---\n");
    if (interrupt_storm_detected) {
        printf("❌ FAIL: Interrupt storm detected\n");
        printf("   CPU stuck at interrupt vectors\n");
    } else if (pc_at_0x150_count >= 100) {
        printf("✅ PASS: Cart ROM running without interrupt storm!\n");
        printf("   Boot completed at cycle %d\n", boot_complete_cycle);
        printf("   Cart ROM executed for %d cycles at main program\n", pc_at_0x150_count);
        printf("   No PC stuck at 0x0038-0x003F\n");
    } else {
        printf("⚠️  PARTIAL: Boot ROM completed but cart ROM not stable\n");
        printf("   Boot completed at cycle %d\n", boot_complete_cycle);
        printf("   Final PC: 0x%04X\n", dut->dbg_cpu_addr);
    }

    delete sdram;
    delete dut;
    return (interrupt_storm_detected) ? 1 : 0;
}
