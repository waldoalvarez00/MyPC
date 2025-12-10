// GameBoy RTL Unit Test - OAM DMA Engine
// Tests for Object Attribute Memory DMA transfers
//
// OAM DMA is triggered by writing to 0xFF46.
// Transfers 160 bytes to OAM (0xFE00-0xFE9F).

#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"

//=============================================================================
// Test: DMA inactive after reset
//=============================================================================
void test_dma_inactive_after_reset(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("OAM DMA Inactive After Reset");

    reset_dut_with_sdram(dut, sdram);

    // Run a few cycles
    run_cycles_with_sdram(dut, sdram, 100);

    // Verify DMA is not active
    results.check_eq(dut->dbg_dma_rd, 0, "dma_rd is 0 after reset");
    results.check_eq(dut->dbg_dma_read_ext_bus, 0, "dma_read_ext_bus is 0 after reset");

    // Run more cycles to ensure it stays inactive
    int dma_rd_count = 0;
    for (int i = 0; i < 500; i++) {
        tick_with_sdram(dut, sdram);
        if (dut->dbg_dma_rd) dma_rd_count++;
    }

    results.check_eq(dma_rd_count, 0, "DMA stays inactive without trigger");
}

//=============================================================================
// Test: DMA signal relationships
//=============================================================================
void test_dma_signal_relationships(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("OAM DMA Signal Relationships");

    reset_dut_with_sdram(dut, sdram);

    // Verify signal relationships over many cycles
    int violations = 0;

    for (int i = 0; i < 1000; i++) {
        tick_with_sdram(dut, sdram);

        // dma_read_ext_bus should only be high when dma_rd is high
        // (can't read external bus if DMA not reading)
        if (dut->dbg_dma_read_ext_bus && !dut->dbg_dma_rd) {
            violations++;
            printf("  [WARN] dma_read_ext_bus=1 but dma_rd=0 at cycle %d\n", i);
        }
    }

    results.check(violations == 0,
                  "dma_read_ext_bus implies dma_rd");
}

//=============================================================================
// Test: DMA does not interfere with CPU
//=============================================================================
void test_dma_cpu_coexistence(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("OAM DMA and CPU Coexistence");

    reset_dut_with_sdram(dut, sdram);
    auto* root = dut->rootp;

    // Disable boot ROM
    root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;

    // Load ROM
    for (int i = 0; i < 0x8000; i += 2) {
        sdram->write16(i, 0x0000);
    }

    // Track CPU activity
    uint16_t last_addr = dut->dbg_cpu_addr;
    int cpu_addr_changes = 0;

    for (int i = 0; i < 2000; i++) {
        root->top__DOT__gameboy__DOT__boot_rom_enabled = 0;
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cpu_addr != last_addr) {
            cpu_addr_changes++;
            last_addr = dut->dbg_cpu_addr;
        }
    }

    // Without OAM DMA trigger, CPU should execute normally
    results.check(cpu_addr_changes > 0, "CPU executes when OAM DMA not active");
    results.check_eq(dut->dbg_dma_rd, 0, "OAM DMA not triggered");

    printf("  [INFO] CPU address changed %d times\n", cpu_addr_changes);
}

//=============================================================================
// Test: DMA and HDMA mutual exclusion
//=============================================================================
void test_dma_hdma_exclusion(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("OAM DMA and HDMA Exclusion");

    reset_dut_with_sdram(dut, sdram);

    // Track simultaneous DMA and HDMA activity
    int simultaneous = 0;

    for (int i = 0; i < 5000; i++) {
        tick_with_sdram(dut, sdram);

        // Both should not be active simultaneously
        if (dut->dbg_dma_rd && dut->dbg_hdma_active) {
            simultaneous++;
        }

        // Both should not access external bus simultaneously
        if (dut->dbg_dma_read_ext_bus && dut->dbg_hdma_read_ext_bus) {
            simultaneous++;
        }
    }

    results.check(simultaneous == 0,
                  "OAM DMA and HDMA never active simultaneously");
}

//=============================================================================
// Test: DMA read signal stability
//=============================================================================
void test_dma_rd_stability(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("OAM DMA Read Signal Stability");

    reset_dut_with_sdram(dut, sdram);

    // Without trigger, dma_rd should stay low
    int transitions = 0;
    int last_dma_rd = dut->dbg_dma_rd;

    for (int i = 0; i < 2000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_dma_rd != last_dma_rd) {
            transitions++;
            last_dma_rd = dut->dbg_dma_rd;
        }
    }

    // Without trigger, should see no transitions
    results.check(transitions == 0, "dma_rd stable when not triggered");
}

//=============================================================================
// Test: DMA external bus signal stability
//=============================================================================
void test_dma_ext_bus_stability(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("OAM DMA External Bus Stability");

    reset_dut_with_sdram(dut, sdram);

    // Without trigger, dma_read_ext_bus should stay low
    int transitions = 0;
    int last_dma_ext = dut->dbg_dma_read_ext_bus;

    for (int i = 0; i < 2000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_dma_read_ext_bus != last_dma_ext) {
            transitions++;
            last_dma_ext = dut->dbg_dma_read_ext_bus;
        }
    }

    results.check(transitions == 0, "dma_read_ext_bus stable when not triggered");
}

//=============================================================================
// Main
//=============================================================================
int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("GameBoy OAM DMA Engine Unit Tests\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->debug = false;

    TestResults results;
    results.current_suite = "OAM DMA Engine Tests";

    // Run all test suites
    test_dma_inactive_after_reset(dut, sdram, results);
    test_dma_signal_relationships(dut, sdram, results);
    test_dma_cpu_coexistence(dut, sdram, results);
    test_dma_hdma_exclusion(dut, sdram, results);
    test_dma_rd_stability(dut, sdram, results);
    test_dma_ext_bus_stability(dut, sdram, results);

    // Cleanup
    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
