// ROM Loader Model Testbench for Verilator
// Tests ROM loading and transfer to SDRAM model
//
// Build: make -f Makefile.rom
// Run: ./obj_dir/Vrom_transfer_sim

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vrom_transfer_sim.h"
#include "../sim/rom_loader.h"
#include "../sim/sdram_model_cpp.h"

#define CLK_PERIOD 20  // 50 MHz

class ROMLoaderTestbench {
public:
    Vrom_transfer_sim* dut;
    ROMLoader* loader;
    SDRAMModelCpp* sdram;
    VerilatedVcdC* trace;
    vluint64_t sim_time;
    int pass_count;
    int fail_count;

    ROMLoaderTestbench(bool debug = false) {
        dut = new Vrom_transfer_sim;
        loader = new ROMLoader(debug);
        sdram = new SDRAMModelCpp(debug);
        trace = nullptr;
        sim_time = 0;
        pass_count = 0;
        fail_count = 0;
    }

    ~ROMLoaderTestbench() {
        if (trace) {
            trace->close();
            delete trace;
        }
        delete dut;
        delete loader;
        delete sdram;
    }

    void openTrace(const char* filename) {
        Verilated::traceEverOn(true);
        trace = new VerilatedVcdC;
        dut->trace(trace, 99);
        trace->open(filename);
    }

    void tick() {
        // Rising edge
        dut->clk = 1;
        dut->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;

        // Drive SDRAM model
        uint16_t sdram_dq = sdram->tick(
            dut->sd_cs,
            dut->sd_ras,
            dut->sd_cas,
            dut->sd_we,
            dut->sd_ba,
            dut->sd_addr,
            dut->sd_dqm,
            dut->sd_dq_out
        );

        // Feed SDRAM output back to DUT
        if (sdram->isOutputEnabled()) {
            dut->sd_dq_in = sdram_dq;
        } else {
            dut->sd_dq_in = 0xFFFF;
        }

        // Falling edge
        dut->clk = 0;
        dut->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;
    }

    void reset() {
        dut->reset = 1;
        dut->start = 0;
        dut->data_in = 0;
        dut->data_valid = 0;
        dut->addr_in = 0;

        for (int i = 0; i < 10; i++) {
            tick();
        }

        dut->reset = 0;
    }

    // Transfer ROM data to DUT which writes to SDRAM
    int transferROM(uint32_t dest_addr = 0) {
        loader->startTransfer(dest_addr);

        uint32_t addr;
        uint16_t data;
        int transfers = 0;

        // Start transfer
        dut->start = 1;
        tick();
        dut->start = 0;

        while (loader->getNextWord(addr, data)) {
            // Wait for DUT to be ready
            int timeout = 100;
            while (!dut->ready && timeout-- > 0) {
                tick();
            }

            if (timeout <= 0) {
                printf("ERROR: Transfer timeout at 0x%08X\n", addr);
                return -1;
            }

            // Send data to DUT
            dut->addr_in = addr >> 1;  // Word address
            dut->data_in = data;
            dut->data_valid = 1;
            tick();
            dut->data_valid = 0;

            // Wait for write to complete
            timeout = 50;
            while (dut->busy && timeout-- > 0) {
                tick();
            }

            transfers++;
        }

        // Wait for any pending operations
        for (int i = 0; i < 20; i++) {
            tick();
        }

        return transfers;
    }

    // Direct transfer to SDRAM (bypass DUT)
    int directTransfer(uint32_t dest_addr = 0) {
        loader->startTransfer(dest_addr);

        uint32_t addr;
        uint8_t data;
        int transfers = 0;

        while (loader->getNextByte(addr, data)) {
            sdram->pokeByte(addr, data);
            transfers++;
        }

        return transfers;
    }

    // Verify SDRAM contents against ROM
    int verifySDRAM(uint32_t start_addr = 0) {
        int errors = 0;
        uint32_t size = loader->getSize();

        for (uint32_t i = 0; i < size; i++) {
            uint8_t expected = loader->readByte(i);
            uint8_t actual = sdram->peekByte(start_addr + i);

            if (actual != expected) {
                if (errors < 10) {
                    printf("  Verify error at 0x%08X: expected 0x%02X, got 0x%02X\n",
                           start_addr + i, expected, actual);
                }
                errors++;
            }
        }

        return errors;
    }

    void reportTest(const char* name, bool pass) {
        if (pass) {
            printf("PASS: %s\n", name);
            pass_count++;
        } else {
            printf("FAIL: %s\n", name);
            fail_count++;
        }
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    bool debug = false;
    bool enable_trace = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--trace") == 0) {
            enable_trace = true;
        }
        if (strcmp(argv[i], "--debug") == 0) {
            debug = true;
        }
    }

    ROMLoaderTestbench tb(debug);

    if (enable_trace) {
        tb.openTrace("rom_test.vcd");
        printf("Tracing enabled - output to rom_test.vcd\n");
    }

    printf("\n========================================\n");
    printf("ROM Loader Model Testbench\n");
    printf("========================================\n\n");

    // Reset
    tb.reset();
    printf("System reset complete\n");

    // Test 1: Generate and load small test ROM
    printf("\n--- Test: Generate small test ROM ---\n");
    {
        tb.loader->generateTestROM(1024, 0);  // 1KB, incrementing pattern
        bool pass = (tb.loader->getSize() == 1024);
        printf("  Generated %u byte test ROM\n", tb.loader->getSize());
        tb.reportTest("Generate small test ROM", pass);
    }

    // Test 2: Direct transfer to SDRAM
    printf("\n--- Test: Direct transfer to SDRAM ---\n");
    {
        int bytes = tb.directTransfer(0x0000);
        bool pass = (bytes == 1024);
        printf("  Transferred %d bytes\n", bytes);
        tb.reportTest("Direct transfer to SDRAM", pass);
    }

    // Test 3: Verify SDRAM contents
    printf("\n--- Test: Verify SDRAM contents ---\n");
    {
        int errors = tb.verifySDRAM(0x0000);
        bool pass = (errors == 0);
        printf("  Verification errors: %d\n", errors);
        tb.reportTest("Verify SDRAM contents", pass);
    }

    // Test 4: Generate larger test ROM
    printf("\n--- Test: Generate 32KB test ROM ---\n");
    {
        tb.loader->generateTestROM(32 * 1024, 1);  // 32KB, XOR pattern
        bool pass = (tb.loader->getSize() == 32 * 1024);
        printf("  Generated %u byte test ROM\n", tb.loader->getSize());
        tb.reportTest("Generate 32KB test ROM", pass);
    }

    // Test 5: Direct transfer to different address
    printf("\n--- Test: Transfer to offset address ---\n");
    {
        tb.sdram->clear();  // Clear SDRAM first
        int bytes = tb.directTransfer(0x10000);  // 64KB offset
        bool pass = (bytes == 32 * 1024);
        printf("  Transferred %d bytes to 0x10000\n", bytes);
        tb.reportTest("Transfer to offset address", pass);
    }

    // Test 6: Verify at offset
    printf("\n--- Test: Verify at offset address ---\n");
    {
        int errors = tb.verifySDRAM(0x10000);
        bool pass = (errors == 0);
        printf("  Verification errors: %d\n", errors);
        tb.reportTest("Verify at offset address", pass);
    }

    // Test 7: Generate Gameboy-style ROM
    printf("\n--- Test: Generate Gameboy-style ROM ---\n");
    {
        tb.loader->generateTestROM(32 * 1024, 2);  // GB pattern with header
        const ROMLoader::ROMInfo& info = tb.loader->getInfo();
        bool pass = (!info.title.empty());
        printf("  Title: %s\n", info.title.c_str());
        printf("  Banks: %u\n", info.num_banks);
        tb.reportTest("Generate Gameboy-style ROM", pass);
    }

    // Test 8: Transfer via RTL (if DUT supports it)
    printf("\n--- Test: Transfer via RTL DUT ---\n");
    {
        tb.sdram->clear();
        tb.reset();
        tb.loader->generateTestROM(256, 0);  // Small ROM for quick test
        int transfers = tb.transferROM(0x0000);
        bool pass = (transfers > 0);
        printf("  Completed %d word transfers\n", transfers);
        tb.reportTest("Transfer via RTL DUT", pass);
    }

    // Test 9: Verify RTL transfer
    printf("\n--- Test: Verify RTL transfer ---\n");
    {
        int errors = tb.verifySDRAM(0x0000);
        bool pass = (errors == 0);
        printf("  Verification errors: %d\n", errors);
        tb.reportTest("Verify RTL transfer", pass);
    }

    // Test 10: Test ROM info display
    printf("\n--- Test: ROM info display ---\n");
    {
        tb.loader->generateTestROM(64 * 1024, 2);
        tb.loader->dumpInfo();
        bool pass = true;  // Info display test
        tb.reportTest("ROM info display", pass);
    }

    // Test 11: Transfer state machine
    printf("\n--- Test: Transfer state machine ---\n");
    {
        tb.loader->generateTestROM(512, 0);
        tb.loader->startTransfer(0);

        bool was_transferring = tb.loader->isTransferring();
        uint32_t addr;
        uint8_t data;
        while (tb.loader->getNextByte(addr, data)) {
            // Consume all bytes
        }
        bool is_complete = tb.loader->isComplete();

        bool pass = was_transferring && is_complete;
        printf("  State transition: TRANSFERRING -> COMPLETE\n");
        tb.reportTest("Transfer state machine", pass);
    }

    // Final summary
    printf("\n========================================\n");
    printf("Test Summary\n");
    printf("========================================\n");
    printf("Passed: %d\n", tb.pass_count);
    printf("Failed: %d\n", tb.fail_count);
    printf("Total:  %d\n", tb.pass_count + tb.fail_count);

    if (tb.fail_count == 0) {
        printf("\nSUCCESS: All tests passed!\n\n");
    } else {
        printf("\nFAILURE: %d test(s) failed\n\n", tb.fail_count);
    }

    return tb.fail_count > 0 ? 1 : 0;
}
