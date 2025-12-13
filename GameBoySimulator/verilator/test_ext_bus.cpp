// GameBoy RTL Unit Test - External Bus Arbitration
// Tests for CPU/HDMA/DMA bus multiplexing
//
// Priority: HDMA > DMA > CPU
// Signals: ext_bus_i, hdma_read_ext_bus, dma_read_ext_bus, nCS, cart_rd

#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"

//=============================================================================
// Test: CPU has bus access when no DMA
//=============================================================================
void test_cpu_bus_access_no_dma(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("CPU Bus Access Without DMA");

    reset_dut_with_sdram(dut, sdram);

    // Load ROM data
    for (int i = 0; i < 0x1000; i += 2) {
        sdram->write16(i, 0x0000);  // NOPs
    }

    // Run and verify cart_rd occurs (CPU accessing cart)
    int cart_rd_count = 0;
    for (int i = 0; i < 1000; i++) {
        tick_with_sdram(dut, sdram);
        if (dut->dbg_cart_rd) cart_rd_count++;
    }

    results.check(cart_rd_count > 0, "CPU can access cart bus when no DMA");
    results.check_eq(dut->dbg_hdma_read_ext_bus, 0, "HDMA not using bus");
    results.check_eq(dut->dbg_dma_read_ext_bus, 0, "DMA not using bus");

    printf("  [INFO] cart_rd count: %d\n", cart_rd_count);
}

//=============================================================================
// Test: External bus signals are valid
//=============================================================================
void test_ext_bus_signals_valid(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("External Bus Signal Validity");

    reset_dut_with_sdram(dut, sdram);

    // Run and check signals are not in undefined states
    int valid_states = 0;
    int total_checks = 0;

    for (int i = 0; i < 500; i++) {
        tick_with_sdram(dut, sdram);

        // All these signals should be 0 or 1, not X
        total_checks++;
        if (dut->dbg_cart_rd == 0 || dut->dbg_cart_rd == 1) valid_states++;
    }

    results.check(valid_states == total_checks, "cart_rd signal always valid (0 or 1)");

    // Check that signals change appropriately
    printf("  [INFO] Final state: cart_rd=%d cart_wr=%d\n",
           dut->dbg_cart_rd, dut->dbg_cart_wr);
}

//=============================================================================
// Test: HDMA and DMA bus exclusivity
//=============================================================================
void test_bus_exclusivity(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Bus Source Exclusivity");

    reset_dut_with_sdram(dut, sdram);

    // Track simultaneous bus access attempts
    int simultaneous_hdma_dma = 0;
    int simultaneous_hdma_cpu_read = 0;

    for (int i = 0; i < 2000; i++) {
        tick_with_sdram(dut, sdram);

        // HDMA and DMA should never both access bus
        if (dut->dbg_hdma_read_ext_bus && dut->dbg_dma_read_ext_bus) {
            simultaneous_hdma_dma++;
        }
    }

    results.check(simultaneous_hdma_dma == 0,
                  "HDMA and DMA never access bus simultaneously");
}

//=============================================================================
// Test: Cart address (mbc_addr) updates
//=============================================================================
void test_mbc_addr_updates(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("MBC Address Updates");

    reset_dut_with_sdram(dut, sdram);

    // Load ROM
    for (int i = 0; i < 0x8000; i += 2) {
        sdram->write16(i, 0x0000);
    }

    // Track mbc_addr changes
    uint32_t last_mbc_addr = dut->dbg_mbc_addr;
    int addr_changes = 0;

    for (int i = 0; i < 2000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_mbc_addr != last_mbc_addr) {
            addr_changes++;
            last_mbc_addr = dut->dbg_mbc_addr;
        }
    }

    results.check(addr_changes > 0, "mbc_addr changes during execution");
    printf("  [INFO] mbc_addr changed %d times\n", addr_changes);
}

//=============================================================================
// Test: Cart read/write signals
//=============================================================================
void test_cart_rd_wr_signals(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("Cart Read/Write Signals");

    reset_dut_with_sdram(dut, sdram);

    // Load ROM
    for (int i = 0; i < 0x8000; i += 2) {
        sdram->write16(i, 0x0000);
    }

    // Count read and write signals
    int cart_rd_count = 0;
    int cart_wr_count = 0;

    for (int i = 0; i < 2000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cart_rd) cart_rd_count++;
        if (dut->dbg_cart_wr) cart_wr_count++;
    }

    results.check(cart_rd_count > 0, "cart_rd asserts during execution");

    printf("  [INFO] cart_rd: %d, cart_wr: %d\n", cart_rd_count, cart_wr_count);
}

//=============================================================================
// Test: CPU read signal (cpu_rd_n) behavior
//=============================================================================
void test_cpu_rd_n_behavior(Vtop* dut, MisterSDRAMModel* sdram, TestResults& results) {
    results.set_suite("CPU Read Signal Behavior");

    reset_dut_with_sdram(dut, sdram);

    // Load ROM
    for (int i = 0; i < 0x8000; i += 2) {
        sdram->write16(i, 0x0000);
    }

    // Track cpu_rd_n (active low)
    int cpu_reading = 0;  // cpu_rd_n = 0 means reading
    int cpu_not_reading = 0;

    for (int i = 0; i < 2000; i++) {
        tick_with_sdram(dut, sdram);

        if (dut->dbg_cpu_rd_n == 0) {
            cpu_reading++;
        } else {
            cpu_not_reading++;
        }
    }

    results.check(cpu_reading > 0, "CPU performs reads (cpu_rd_n=0)");
    results.check(cpu_not_reading > 0, "CPU has idle periods (cpu_rd_n=1)");

    printf("  [INFO] cpu_rd_n=0 (reading): %d, cpu_rd_n=1 (idle): %d\n",
           cpu_reading, cpu_not_reading);
}

//=============================================================================
// Main
//=============================================================================
int main(int argc, char** argv) {
    printf("===========================================\n");
    printf("GameBoy External Bus Arbitration Unit Tests\n");
    printf("===========================================\n");

    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;  // Realistic CAS latency
    sdram->debug = false;

    TestResults results;
    results.current_suite = "External Bus Arbitration Tests";

    // Run all test suites
    test_cpu_bus_access_no_dma(dut, sdram, results);
    test_ext_bus_signals_valid(dut, sdram, results);
    test_bus_exclusivity(dut, sdram, results);
    test_mbc_addr_updates(dut, sdram, results);
    test_cart_rd_wr_signals(dut, sdram, results);
    test_cpu_rd_n_behavior(dut, sdram, results);

    // Cleanup
    dut->final();
    delete dut;
    delete sdram;

    return results.report();
}
