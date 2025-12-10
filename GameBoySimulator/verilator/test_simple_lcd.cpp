// Simple LCD Enable Test
// Tests if writing to LCDC (0xFF40) works

#include <verilated.h>
#include "verilated_vcd_c.h"
#include "Vtop.h"
#include "Vtop___024root.h"
#include "../sim/mister_sdram_model.h"
#include "simple_lcd_rom.h"

Vtop* top = nullptr;
MisterSDRAMModel* sdram = nullptr;
VerilatedVcdC* tfp = nullptr;
vluint64_t main_time = 0;
int clk = 0;

// CRITICAL: rdata must be persistent across calls so SDRAM read data holds stable
uint16_t sdram_rdata = 0;
bool sdram_compl = false;
bool sdram_config_done = false;

void processSDRAM() {
    sdram->processNativeSDRAM(
        top->sd_cs, top->sd_ras, top->sd_cas, top->sd_we,
        top->sd_ba, top->sd_addr, top->sd_data_out, top->sd_dqm,
        sdram_rdata, sdram_compl, sdram_config_done
    );
    top->sd_data_in = sdram_rdata;

    // Debug: Show when sd_data_in changes (disabled for clearer trace)
    // static uint16_t last_sd_data_in = 0xFFFF;
    // if (sdram_rdata != last_sd_data_in) {
    //     printf("[Cycle %4llu] sd_data_in updated: 0x%04X → 0x%04X\n",
    //            main_time, last_sd_data_in, sdram_rdata);
    //     last_sd_data_in = sdram_rdata;
    // }
}

void tick() {
    clk = !clk;
    top->clk_sys = clk;
    top->eval();
    // Only trace cycles 200-450 to keep VCD file small
    if (tfp && main_time >= 200 && main_time < 450) tfp->dump(main_time);
    if (clk) {
        processSDRAM();
        main_time++;
    }
    if (tfp && main_time >= 200 && main_time < 450) tfp->dump(main_time);
}

int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("Simple LCD Enable Test\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);
    top = new Vtop();
    sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->debug = false;  // Disable SDRAM debug output

    auto* root = top->rootp;

    // Enable VCD tracing
    tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open("trace.vcd");
    printf("VCD tracing enabled - output to trace.vcd\n");

    // Initialize
    top->reset = 1;
    top->ioctl_download = 0;
    top->ioctl_wr = 0;
    top->ioctl_addr = 0;
    top->ioctl_dout = 0;
    top->ioctl_index = 0;
    top->inputs = 0xFF;
    top->boot_download = 0;
    top->boot_wr = 0;
    top->boot_addr = 0;
    top->boot_data = 0;

    // Initial reset
    printf("Step 1: Initial reset...\n");
    for (int i = 0; i < 100; i++) {
        tick();
    }

    // Load ROM to SDRAM model (fast path - like test_display_fixed)
    printf("Step 2: Loading ROM to SDRAM (%zu bytes)...\n", sizeof(simple_lcd_rom));
    for (size_t addr = 0; addr < sizeof(simple_lcd_rom); addr += 2) {
        uint16_t word = simple_lcd_rom[addr];
        if (addr + 1 < sizeof(simple_lcd_rom)) {
            word |= (simple_lcd_rom[addr + 1] << 8);
        }
        sdram->write16(addr, word);
    }

    // Release reset so ce_cpu runs
    printf("Step 3: Releasing reset...\n");
    top->reset = 0;

    // Disable boot ROM
    for (int i = 0; i < 100; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // SDRAM init
    printf("  Running SDRAM init...\n");
    for (int i = 0; i < 2000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // Now do ioctl download to trigger cart_ready (data already loaded via direct writes)
    printf("Step 4: Running ioctl download to set cart_ready...\n");
    top->ioctl_download = 1;
    top->ioctl_index = 0;

    for (size_t addr = 0; addr < sizeof(simple_lcd_rom); addr += 2) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

        uint16_t word = simple_lcd_rom[addr];
        if (addr + 1 < sizeof(simple_lcd_rom)) {
            word |= (simple_lcd_rom[addr + 1] << 8);
        }
        top->ioctl_dout = word;
        top->ioctl_addr = addr;  // Byte address (RTL converts to word address)
        top->ioctl_wr = 1;

        for (int i = 0; i < 32; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }
        top->ioctl_wr = 0;
        for (int i = 0; i < 32; i++) {
            root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
            tick();
        }
    }
    top->ioctl_download = 0;

    for (int i = 0; i < 1000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    printf("  cart_ready=%d\n", top->dbg_cart_ready);

    if (!top->dbg_cart_ready) {
        printf("\n!!! WARNING: cart_ready is still 0!\n");
    }

    // Verify SDRAM contents and boot ROM status
    printf("\nVerifying SDRAM contents at byte addresses:\n");
    for (int addr = 0; addr < 16; addr += 2) {
        uint16_t data = sdram->read16(addr);
        printf("  Byte 0x%04X: 0x%02X 0x%02X (expected: 0x%02X 0x%02X)\n",
               addr, data & 0xFF, (data >> 8) & 0xFF,
               simple_lcd_rom[addr], simple_lcd_rom[addr+1]);
    }

    printf("\nBoot ROM status:\n");
    printf("  boot_rom_enabled = %d\n", root->top__DOT__gameboy__DOT__boot_rom_enabled);

    // Force boot ROM disabled
    printf("  Forcing boot_rom_enabled = 0...\n");
    root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
    for (int i = 0; i < 100; i++) {
        tick();
    }
    printf("  boot_rom_enabled = %d (after forcing)\n", root->top__DOT__gameboy__DOT__boot_rom_enabled);

    // Reset CPU
    printf("\nStep 5: Resetting CPU...\n");
    top->reset = 1;
    for (int i = 0; i < 100; i++) {
        tick();
    }
    top->reset = 0;

    // Monitor PC and ce_cpu immediately after reset
    printf("  Checking PC and ce_cpu after reset release:\n");
    bool ce_cpu_seen = false;
    for (int i = 0; i < 100; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
        uint16_t pc = top->dbg_cpu_addr;
        uint8_t ce_cpu = top->dbg_ce_cpu;
        uint8_t clk_div = root->top__DOT__clk_div;
        uint8_t ce_cpu2x = root->top__DOT__ce_cpu2x;

        if (ce_cpu && !ce_cpu_seen) {
            printf("    *** ce_cpu FIRST HIGH at cycle %d: PC=0x%04X, clk_div=%d, ce_cpu2x=%d\n",
                   i, pc, clk_div, ce_cpu2x);
            ce_cpu_seen = true;
        }
        if (i < 20 || (i < 40 && ce_cpu)) {
            printf("    Cycle %d: PC=0x%04X, ce_cpu=%d, clk_div=%d\n", i, pc, ce_cpu, clk_div);
        }
    }
    if (!ce_cpu_seen) {
        printf("    !!! ce_cpu NEVER went high in 100 cycles!\n");
    }

    for (int i = 0; i < 80; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick();
    }

    // Detailed instruction trace with CPU and SDRAM state
    printf("\nStep 6: Detailed CPU Execution Trace:\n");
    printf("===================================================================================================\n");
    printf("Cycle | PC     | rom_do | M1 | RD | WR |HALT|STOP| ce | cart_rdy | boot_rom | SDRAM        | Notes\n");
    printf("------|--------|--------|----|----|----|----|----|----|----------|----------|--------------|------------------------------------------\n");

    uint16_t last_pc = 0xFFFF;
    uint8_t last_rom_do = 0xFF;
    uint8_t last_m1 = 0xFF;
    uint8_t instruction_bytes[3] = {0};
    int byte_count = 0;
    bool in_instruction = false;

    for (int i = 0; i < 1000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        top->ioctl_download = 0;
        tick();

        // CPU signals
        uint16_t pc = top->dbg_cpu_addr;
        uint8_t rom_do = root->top__DOT__rom_do;
        uint8_t cpu_m1_n = root->top__DOT__gameboy__DOT__cpu_m1_n;
        uint8_t cpu_rd_n = root->top__DOT__gameboy__DOT__cpu_rd_n;
        uint8_t cpu_wr_n = root->top__DOT__gameboy__DOT__cpu_wr_n;
        uint8_t cpu_mreq_n = root->top__DOT__gameboy__DOT__cpu_mreq_n;
        uint8_t cpu_clken = top->dbg_cpu_clken;
        uint8_t ce_cpu = top->dbg_ce_cpu;

        // System signals
        uint8_t cart_ready = top->dbg_cart_ready;
        uint8_t boot_rom_enabled = top->dbg_boot_rom_enabled;
        uint8_t sel_boot_rom = top->dbg_sel_boot_rom;

        // SDRAM signals
        uint8_t cart_rd = root->top__DOT__cart_rd;
        uint8_t sdram_oe = root->top__DOT__sdram_oe;
        uint8_t sdram_state = root->top__DOT__sdram_ctrl__DOT__dbg_state;
        uint16_t sdram_dout = root->top__DOT__sdram_ctrl__DOT__dout;

        // Detect instruction fetch (M1 cycle with MREQ and RD active)
        bool is_m1_fetch = (cpu_m1_n == 0) && (cpu_mreq_n == 0) && (cpu_rd_n == 0);
        bool is_mem_read = (cpu_mreq_n == 0) && (cpu_rd_n == 0) && (cpu_m1_n == 1);

        // Track instruction bytes
        if (is_m1_fetch && (cpu_m1_n != last_m1)) {
            // Start of new instruction
            in_instruction = true;
            byte_count = 0;
            instruction_bytes[0] = rom_do;
            byte_count = 1;
        } else if (in_instruction && is_mem_read && (pc != last_pc)) {
            // Operand byte
            if (byte_count < 3) {
                instruction_bytes[byte_count] = rom_do;
                byte_count++;
            }
        }

        // Show state on ce_cpu pulse or when PC/M1 changes
        if (ce_cpu || (pc != last_pc) || (cpu_m1_n != last_m1)) {
            const char* state_name = "";
            switch(sdram_state) {
                case 0: state_name = "IDLE"; break;
                case 1: state_name = "ACTV"; break;
                case 2: state_name = "READ"; break;
                case 3: state_name = "WRIT"; break;
                case 4: state_name = "REFR"; break;
                case 5: state_name = "PRCH"; break;
                default: state_name = "????"; break;
            }

            // Build notes
            char note[200] = "";
            if (is_m1_fetch) {
                snprintf(note, sizeof(note), "M1: Opcode fetch = 0x%02X", rom_do);
                // Decode common opcodes
                if (rom_do == 0xC3) {
                    if (byte_count >= 3) {
                        uint16_t target = instruction_bytes[1] | (instruction_bytes[2] << 8);
                        snprintf(note, sizeof(note), "M1: JP 0x%04X (read: %02X %02X %02X)",
                                target, instruction_bytes[0], instruction_bytes[1], instruction_bytes[2]);
                    } else {
                        snprintf(note, sizeof(note), "M1: JP nn (opcode, bytes=%d)", byte_count);
                    }
                } else if (rom_do == 0x00) {
                    snprintf(note, sizeof(note), "M1: NOP");
                } else if (rom_do == 0xF3) {
                    snprintf(note, sizeof(note), "M1: DI (disable interrupts)");
                } else if (rom_do == 0x3E) {
                    snprintf(note, sizeof(note), "M1: LD A,n");
                } else if (rom_do == 0xE0) {
                    snprintf(note, sizeof(note), "M1: LDH (n),A");
                }
            } else if (is_mem_read) {
                snprintf(note, sizeof(note), "MEM READ: 0x%02X (byte %d of instruction)", rom_do, byte_count);
            } else if (pc == 0x0150) {
                snprintf(note, sizeof(note), "*** TARGET REACHED! ***");
            } else if (!cpu_clken) {
                snprintf(note, sizeof(note), "CPU clock disabled");
            }

            printf(" %4d | 0x%04X | 0x%02X   | %d  | %d  | %d  | %d  | ?  | %d  |    %d     |  %d / %d   | %-4s/0x%04X | %s\n",
                   i, pc, rom_do,
                   !cpu_m1_n, !cpu_rd_n, !cpu_wr_n,
                   0, // HALT not available
                   cpu_clken, cart_ready, boot_rom_enabled, sel_boot_rom,
                   state_name, sdram_dout, note);

            last_pc = pc;
            last_rom_do = rom_do;
            last_m1 = cpu_m1_n;
        }

        // Stop after reaching target or wrong address
        if (pc == 0x0150) {
            printf("\n*** SUCCESS: Reached target address 0x0150! ***\n");
            break;
        }
        if (pc == 0x01C3) {
            printf("\n*** WRONG ADDRESS: Jumped to 0x01C3 instead of 0x0150 ***\n");
            break;
        }
        if (i > 100 && pc > 0x0010 && pc < 0x0100) {
            printf("\n*** PC advanced past expected range without jumping ***\n");
            break;
        }
    }

    // Check final state
    uint16_t final_pc = top->dbg_cpu_addr;
    uint8_t final_lcdc = root->top__DOT__gameboy__DOT__video__DOT__lcdc;
    uint16_t final_rtl_dout = root->top__DOT__sdram_ctrl__DOT__dout;
    uint8_t final_rom_do = root->top__DOT__rom_do;

    printf("\n=== Final State After 2100 Total Cycles ===\n");
    printf("  PC: 0x%04X\n", final_pc);
    printf("  LCDC: 0x%02X\n", final_lcdc);
    printf("  SDRAM dout: 0x%04X\n", final_rtl_dout);
    printf("  rom_do: 0x%02X\n", final_rom_do);

    // Cleanup
    if (tfp) {
        tfp->close();
        delete tfp;
    }
    top->final();
    delete top;
    delete sdram;

    if (final_lcdc == 0x91) {
        printf("\n=== SUCCESS: LCD enabled correctly! ===\n");
        return 0;
    } else {
        printf("\n=== FAILED: LCDC should be 0x91 but is 0x%02X ===\n", final_lcdc);
        return 1;
    }
}
