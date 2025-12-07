// SDRAM Model Testbench for Verilator
// Tests the sdram_test_top module with SDRAMController + SDRAM model
//
// Build: make sdram_test
// Run: ./obj_dir/Vsdram_test_top

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vsdram_test_top.h"
#include "../sim/sim_sdram.h"

// Clock period in simulation time units (ns)
#define CLK_PERIOD 20  // 50 MHz

// Test timeouts
#define INIT_TIMEOUT 200000  // 200us for initialization
#define OP_TIMEOUT   10000   // 10us for read/write operations

class SDRAMTestbench {
public:
    Vsdram_test_top* top;
    VerilatedVcdC* trace;
    vluint64_t sim_time;
    int pass_count;
    int fail_count;

    SDRAMTestbench() {
        top = new Vsdram_test_top;
        trace = nullptr;
        sim_time = 0;
        pass_count = 0;
        fail_count = 0;
    }

    ~SDRAMTestbench() {
        if (trace) {
            trace->close();
            delete trace;
        }
        delete top;
    }

    void openTrace(const char* filename) {
        Verilated::traceEverOn(true);
        trace = new VerilatedVcdC;
        top->trace(trace, 99);
        trace->open(filename);
    }

    void tick() {
        // Rising edge
        top->clk = 1;
        top->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;

        // Falling edge
        top->clk = 0;
        top->eval();
        if (trace) trace->dump(sim_time);
        sim_time += CLK_PERIOD / 2;
    }

    void reset() {
        top->reset = 1;
        top->h_access = 0;
        top->h_addr = 0;
        top->h_wdata = 0;
        top->h_wr_en = 0;
        top->h_bytesel = 0;

        for (int i = 0; i < 10; i++) {
            tick();
        }

        top->reset = 0;
    }

    bool waitInit() {
        printf("Waiting for SDRAM initialization...\n");
        vluint64_t timeout = sim_time + INIT_TIMEOUT;

        while (sim_time < timeout) {
            tick();
            if (top->h_config_done) {
                printf("SDRAM initialized at %lu ns\n", (unsigned long)sim_time);
                return true;
            }
        }

        printf("ERROR: SDRAM initialization timeout\n");
        return false;
    }

    bool write(uint32_t addr, uint16_t data, uint8_t bytesel = 3) {
        top->h_addr = addr >> 1;  // Convert byte address to word address
        top->h_wdata = data;
        top->h_wr_en = 1;
        top->h_bytesel = bytesel;
        top->h_access = 1;

        vluint64_t timeout = sim_time + OP_TIMEOUT;
        while (sim_time < timeout) {
            tick();
            if (top->h_compl) {
                top->h_access = 0;
                top->h_wr_en = 0;
                tick();
                return true;
            }
        }

        printf("ERROR: Write timeout at address 0x%08X\n", addr);
        top->h_access = 0;
        top->h_wr_en = 0;
        return false;
    }

    bool read(uint32_t addr, uint16_t* data, uint8_t bytesel = 3) {
        top->h_addr = addr >> 1;
        top->h_wr_en = 0;
        top->h_bytesel = bytesel;
        top->h_access = 1;

        vluint64_t timeout = sim_time + OP_TIMEOUT;
        while (sim_time < timeout) {
            tick();
            if (top->h_compl) {
                *data = top->h_rdata;
                top->h_access = 0;
                tick();
                return true;
            }
        }

        printf("ERROR: Read timeout at address 0x%08X\n", addr);
        top->h_access = 0;
        return false;
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

    SDRAMTestbench tb;

    // Enable waveform tracing
    bool enable_trace = false;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--trace") == 0) {
            enable_trace = true;
        }
    }

    if (enable_trace) {
        tb.openTrace("sdram_test.vcd");
        printf("Tracing enabled - output to sdram_test.vcd\n");
    }

    printf("\n========================================\n");
    printf("SDRAM Verilator Model Testbench\n");
    printf("========================================\n\n");

    // Reset
    tb.reset();

    // Wait for initialization
    if (!tb.waitInit()) {
        return 1;
    }
    tb.reportTest("Initialization", true);

    // Test 1: Single word write and read
    printf("\n--- Test: Single word write/read ---\n");
    {
        uint16_t data;
        bool pass = tb.write(0x1000, 0xDEAD);
        pass = pass && tb.read(0x1000, &data);
        pass = pass && (data == 0xDEAD);
        printf("  Write 0xDEAD to 0x1000, read back: 0x%04X\n", data);
        tb.reportTest("Single word write/read", pass);
    }

    // Test 2: Different address
    printf("\n--- Test: Different address ---\n");
    {
        uint16_t data;
        bool pass = tb.write(0x2000, 0xBEEF);
        pass = pass && tb.read(0x2000, &data);
        pass = pass && (data == 0xBEEF);
        printf("  Write 0xBEEF to 0x2000, read back: 0x%04X\n", data);
        tb.reportTest("Different address", pass);
    }

    // Test 3: Verify first write still intact
    printf("\n--- Test: Memory persistence ---\n");
    {
        uint16_t data;
        bool pass = tb.read(0x1000, &data);
        pass = pass && (data == 0xDEAD);
        printf("  Re-read 0x1000: 0x%04X\n", data);
        tb.reportTest("Memory persistence", pass);
    }

    // Test 4: Byte write - low byte only
    printf("\n--- Test: Byte write (low byte) ---\n");
    {
        uint16_t data;
        tb.write(0x3000, 0x1234);
        tb.write(0x3000, 0xFF56, 0x01);  // Write only low byte
        tb.read(0x3000, &data);
        bool pass = (data == 0x1256);
        printf("  Expected 0x1256, got: 0x%04X\n", data);
        tb.reportTest("Byte write (low byte)", pass);
    }

    // Test 5: Byte write - high byte only
    printf("\n--- Test: Byte write (high byte) ---\n");
    {
        uint16_t data;
        tb.write(0x3002, 0x5678);
        tb.write(0x3002, 0xABFF, 0x02);  // Write only high byte
        tb.read(0x3002, &data);
        bool pass = (data == 0xAB78);
        printf("  Expected 0xAB78, got: 0x%04X\n", data);
        tb.reportTest("Byte write (high byte)", pass);
    }

    // Test 6: Sequential writes (same row)
    printf("\n--- Test: Sequential writes (same row) ---\n");
    {
        bool pass = true;
        uint16_t data;
        for (int i = 0; i < 8; i++) {
            tb.write(0x4000 + i * 2, 0xA000 + i);
        }
        for (int i = 0; i < 8; i++) {
            tb.read(0x4000 + i * 2, &data);
            if (data != 0xA000 + i) {
                printf("  Mismatch at 0x%04X: expected 0x%04X, got 0x%04X\n",
                       0x4000 + i * 2, 0xA000 + i, data);
                pass = false;
            }
        }
        tb.reportTest("Sequential writes (same row)", pass);
    }

    // Test 7: Different banks
    printf("\n--- Test: Different banks ---\n");
    {
        bool pass = true;
        uint16_t data;

        // Write to different banks (bank select is in address bits)
        tb.write(0x00000, 0x1111);  // Bank 0
        tb.write(0x01000, 0x2222);  // Bank 0 or 1 depending on mapping
        tb.write(0x02000, 0x3333);
        tb.write(0x04000, 0x4444);

        tb.read(0x00000, &data); pass = pass && (data == 0x1111);
        tb.read(0x01000, &data); pass = pass && (data == 0x2222);
        tb.read(0x02000, &data); pass = pass && (data == 0x3333);
        tb.read(0x04000, &data); pass = pass && (data == 0x4444);

        tb.reportTest("Different banks", pass);
    }

    // Test 8: Large address range
    printf("\n--- Test: Large address range ---\n");
    {
        bool pass = true;
        uint16_t data;

        // Test various address ranges
        uint32_t test_addrs[] = {
            0x000000, 0x010000, 0x100000, 0x200000,
            0x400000, 0x800000, 0x1000000, 0x2000000
        };

        for (int i = 0; i < 8; i++) {
            uint32_t addr = test_addrs[i];
            uint16_t val = 0x8000 | i;
            tb.write(addr, val);
            tb.read(addr, &data);
            if (data != val) {
                printf("  Mismatch at 0x%08X: expected 0x%04X, got 0x%04X\n",
                       addr, val, data);
                pass = false;
            }
        }
        tb.reportTest("Large address range", pass);
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
