// MiSTer Generic SDRAM Model Testbench
// Tests both Native SDRAM and Avalon-MM interfaces

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vmister_sdram_ctrl_sim.h"
#include "mister_sdram_model.h"
#include <cstdio>
#include <cstdlib>
#include <cstring>

class MisterSDRAMTestbench {
public:
    Vmister_sdram_ctrl_sim* dut;
    MisterSDRAMModel* sdram;
    VerilatedVcdC* tfp;
    uint64_t main_time;
    bool debug;

    int tests_passed;
    int tests_failed;

    MisterSDRAMTestbench() {
        dut = new Vmister_sdram_ctrl_sim();
        sdram = new MisterSDRAMModel(32, INTERFACE_NATIVE_SDRAM);
        tfp = nullptr;
        main_time = 0;
        debug = false;
        tests_passed = 0;
        tests_failed = 0;
    }

    ~MisterSDRAMTestbench() {
        if (tfp) {
            tfp->close();
            delete tfp;
        }
        delete dut;
        delete sdram;
    }

    void enableTrace(const char* filename) {
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open(filename);
    }

    void tick() {
        // Rising edge
        dut->clk = 1;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        // Process SDRAM commands from controller to model
        uint16_t rdata = 0;
        bool compl_signal = false;
        bool config_done = false;

        sdram->processNativeSDRAM(
            dut->s_cs_n, dut->s_ras_n, dut->s_cas_n, dut->s_we_n,
            dut->s_ba, dut->s_addr,
            dut->s_dq_out, dut->s_dqm,
            rdata, compl_signal, config_done
        );

        // Feed data back from model to controller
        dut->s_dq_in = rdata;

        // Falling edge
        dut->clk = 0;
        dut->eval();
        if (tfp) tfp->dump(main_time++);
    }

    void reset() {
        dut->reset = 1;
        dut->h_addr = 0;
        dut->h_wdata = 0;
        dut->h_wr_en = 0;
        dut->h_bytesel = 0b11;
        dut->h_access = 0;
        dut->av_address = 0;
        dut->av_burstcount = 1;
        dut->av_read = 0;
        dut->av_write = 0;
        dut->av_writedata = 0;
        dut->av_byteenable = 0xFF;

        for (int i = 0; i < 10; i++) tick();

        dut->reset = 0;
        sdram->reset();

        if (debug) printf("SDRAM: Reset complete\n");
    }

    void waitConfigDone() {
        // Wait for SDRAM initialization to complete
        int timeout = 10000;
        while (!dut->h_config_done && timeout > 0) {
            tick();
            timeout--;
        }

        if (timeout == 0) {
            printf("ERROR: Timeout waiting for config_done\n");
        } else if (debug) {
            printf("SDRAM: Configuration done\n");
        }
    }

    // Native SDRAM write operation
    void nativeWrite(uint32_t addr, uint16_t data, uint8_t bytesel = 0b11) {
        dut->h_addr = addr >> 1;  // Convert to word address
        dut->h_wdata = data;
        dut->h_wr_en = 1;
        dut->h_bytesel = bytesel;
        dut->h_access = 1;

        // Wait for completion
        int timeout = 100;
        while (!dut->h_compl && timeout > 0) {
            tick();
            timeout--;
        }

        dut->h_access = 0;
        dut->h_wr_en = 0;
        tick();

        if (timeout == 0) {
            printf("ERROR: Write timeout at addr 0x%06X\n", addr);
        }
    }

    // Native SDRAM read operation
    uint16_t nativeRead(uint32_t addr) {
        dut->h_addr = addr >> 1;  // Convert to word address
        dut->h_wr_en = 0;
        dut->h_bytesel = 0b11;
        dut->h_access = 1;

        // Wait for completion
        int timeout = 100;
        while (!dut->h_compl && timeout > 0) {
            tick();
            timeout--;
        }

        uint16_t data = dut->h_rdata;
        dut->h_access = 0;
        tick();

        if (timeout == 0) {
            printf("ERROR: Read timeout at addr 0x%06X\n", addr);
        }

        return data;
    }

    // Avalon write operation
    void avalonWrite(uint32_t addr, uint64_t data, uint8_t byteenable = 0xFF) {
        dut->av_address = addr;
        dut->av_writedata = data;
        dut->av_byteenable = byteenable;
        dut->av_burstcount = 1;
        dut->av_write = 1;

        tick();
        while (dut->av_waitrequest) tick();

        dut->av_write = 0;
        tick();
    }

    // Avalon read operation
    uint64_t avalonRead(uint32_t addr) {
        dut->av_address = addr;
        dut->av_burstcount = 1;
        dut->av_read = 1;

        tick();
        while (dut->av_waitrequest) tick();

        dut->av_read = 0;

        // Wait for data valid
        int timeout = 100;
        while (!dut->av_readdatavalid && timeout > 0) {
            tick();
            timeout--;
        }

        uint64_t data = dut->av_readdata;
        tick();

        return data;
    }

    void testPass(const char* name) {
        printf("[PASS] %s\n", name);
        tests_passed++;
    }

    void testFail(const char* name, const char* reason) {
        printf("[FAIL] %s: %s\n", name, reason);
        tests_failed++;
    }

    // ===============================================
    // Test Cases
    // ===============================================

    void testInitialization() {
        reset();
        waitConfigDone();

        if (dut->h_config_done) {
            testPass("Initialization");
        } else {
            testFail("Initialization", "Config not done");
        }
    }

    void testBasicWrite() {
        reset();
        waitConfigDone();

        nativeWrite(0x1000, 0xABCD);

        // Verify in model
        uint16_t expected = sdram->read16(0x1000);
        if (expected == 0xABCD) {
            testPass("Basic write");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0xABCD, got 0x%04X", expected);
            testFail("Basic write", buf);
        }
    }

    void testBasicRead() {
        reset();
        waitConfigDone();

        // Pre-load data in model
        sdram->write16(0x2000, 0x1234);

        uint16_t data = nativeRead(0x2000);
        if (data == 0x1234) {
            testPass("Basic read");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0x1234, got 0x%04X", data);
            testFail("Basic read", buf);
        }
    }

    void testWriteRead() {
        reset();
        waitConfigDone();

        // Write multiple locations
        nativeWrite(0x0000, 0x1111);
        nativeWrite(0x1000, 0x2222);
        nativeWrite(0x2000, 0x3333);
        nativeWrite(0x3000, 0x4444);

        // Read back
        bool ok = true;
        if (nativeRead(0x0000) != 0x1111) ok = false;
        if (nativeRead(0x1000) != 0x2222) ok = false;
        if (nativeRead(0x2000) != 0x3333) ok = false;
        if (nativeRead(0x3000) != 0x4444) ok = false;

        if (ok) {
            testPass("Write/Read multiple");
        } else {
            testFail("Write/Read multiple", "Data mismatch");
        }
    }

    void testByteSelect() {
        reset();
        waitConfigDone();

        // Write full word
        nativeWrite(0x4000, 0xFFFF);

        // Write low byte only
        nativeWrite(0x4000, 0x00AA, 0b01);
        uint16_t data = nativeRead(0x4000);

        if ((data & 0x00FF) == 0x00AA && (data & 0xFF00) == 0xFF00) {
            testPass("Byte select (low)");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0xFFAA, got 0x%04X", data);
            testFail("Byte select (low)", buf);
        }
    }

    void testRowHit() {
        reset();
        waitConfigDone();

        // Access same row multiple times
        uint64_t initial_hits = sdram->row_hits;
        uint64_t initial_misses = sdram->row_misses;

        nativeWrite(0x1000, 0x1111);  // First access opens row
        nativeWrite(0x1002, 0x2222);  // Same row
        nativeWrite(0x1004, 0x3333);  // Same row
        nativeWrite(0x1006, 0x4444);  // Same row

        // Should have row hits after first access
        if (sdram->row_hits > initial_hits) {
            testPass("Row hit optimization");
        } else {
            testFail("Row hit optimization", "No row hits detected");
        }
    }

    void testBankInterleave() {
        reset();
        waitConfigDone();

        // Access different banks
        // Bank 0
        nativeWrite(0x00000, 0x0000);
        // Bank 1 (32MB layout: bank at bits 11:10)
        nativeWrite(0x00800, 0x0001);
        // Bank 2
        nativeWrite(0x01000, 0x0002);
        // Bank 3
        nativeWrite(0x01800, 0x0003);

        bool ok = true;
        if (nativeRead(0x00000) != 0x0000) ok = false;
        if (nativeRead(0x00800) != 0x0001) ok = false;
        if (nativeRead(0x01000) != 0x0002) ok = false;
        if (nativeRead(0x01800) != 0x0003) ok = false;

        if (ok) {
            testPass("Bank interleave");
        } else {
            testFail("Bank interleave", "Data mismatch");
        }
    }

    void testLargeAddress() {
        reset();
        waitConfigDone();

        // Test high addresses (near 32MB limit)
        uint32_t addr = 0x1F00000;  // ~31MB
        nativeWrite(addr, 0xBEEF);

        uint16_t data = nativeRead(addr);
        if (data == 0xBEEF) {
            testPass("Large address");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0xBEEF, got 0x%04X", data);
            testFail("Large address", buf);
        }
    }

    void testBurstPattern() {
        reset();
        waitConfigDone();

        // Write sequential pattern
        for (int i = 0; i < 16; i++) {
            nativeWrite(0x5000 + i * 2, 0x5000 + i);
        }

        // Read back and verify
        bool ok = true;
        for (int i = 0; i < 16; i++) {
            uint16_t data = nativeRead(0x5000 + i * 2);
            if (data != (0x5000 + i)) {
                ok = false;
                break;
            }
        }

        if (ok) {
            testPass("Burst pattern");
        } else {
            testFail("Burst pattern", "Data mismatch");
        }
    }

    void testAvalonWrite() {
        reset();
        waitConfigDone();

        // Test model's Avalon interface directly
        uint8_t writedata[8] = {0x78, 0x56, 0x34, 0x12, 0xEF, 0xBE, 0xAD, 0xDE};
        uint8_t readdata[8] = {0};
        bool readdatavalid = false;
        bool waitrequest_out = false;

        // Write via model's Avalon interface
        sdram->processAvalon(false, true, 0x100, 1, writedata, 0xFF,
                            readdata, readdatavalid, waitrequest_out);

        // Verify in model memory
        uint64_t expected = 0;
        for (int i = 0; i < 8; i++) {
            expected |= ((uint64_t)sdram->read8(0x100 * 8 + i)) << (i * 8);
        }

        if (expected == 0xDEADBEEF12345678ULL) {
            testPass("Avalon write");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0xDEADBEEF12345678, got 0x%016lX", (unsigned long)expected);
            testFail("Avalon write", buf);
        }
    }

    void testAvalonRead() {
        reset();
        waitConfigDone();

        // Pre-load via model
        uint64_t test_data = 0xCAFEBABE87654321ULL;
        for (int i = 0; i < 8; i++) {
            sdram->write8(0x200 * 8 + i, (test_data >> (i * 8)) & 0xFF);
        }

        // Read via model's Avalon interface
        uint8_t writedata[8] = {0};
        uint8_t readdata[8] = {0};
        bool readdatavalid = false;
        bool waitrequest_out = false;

        // Issue read
        sdram->processAvalon(true, false, 0x200, 1, writedata, 0xFF,
                            readdata, readdatavalid, waitrequest_out);

        // Process latency cycles
        for (int i = 0; i < 5; i++) {
            sdram->processAvalon(false, false, 0, 0, writedata, 0,
                                readdata, readdatavalid, waitrequest_out);
            if (readdatavalid) break;
        }

        uint64_t data = 0;
        for (int i = 0; i < 8; i++) {
            data |= ((uint64_t)readdata[i]) << (i * 8);
        }

        if (data == test_data) {
            testPass("Avalon read");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0xCAFEBABE87654321, got 0x%016lX", (unsigned long)data);
            testFail("Avalon read", buf);
        }
    }

    void testRefresh() {
        reset();
        waitConfigDone();

        // Run many cycles to trigger auto-refresh
        uint64_t initial_refresh = sdram->refresh_count;

        for (int i = 0; i < 1000; i++) {
            tick();
        }

        if (sdram->refresh_count > initial_refresh) {
            testPass("Auto-refresh");
        } else {
            testFail("Auto-refresh", "No refresh detected");
        }
    }

    void runAllTests() {
        printf("\n=== MiSTer Generic SDRAM Model Tests ===\n\n");

        testInitialization();
        testBasicWrite();
        testBasicRead();
        testWriteRead();
        testByteSelect();
        testRowHit();
        testBankInterleave();
        testLargeAddress();
        testBurstPattern();
        testAvalonWrite();
        testAvalonRead();
        testRefresh();

        printf("\n=== Test Summary ===\n");
        printf("Passed: %d\n", tests_passed);
        printf("Failed: %d\n", tests_failed);
        printf("Total:  %d\n", tests_passed + tests_failed);

        sdram->printStats();
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    MisterSDRAMTestbench tb;

    // Check for debug flag
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--debug") == 0) {
            tb.debug = true;
            tb.sdram->debug = true;
        }
        if (strcmp(argv[i], "--trace") == 0) {
            tb.enableTrace("mister_sdram_test.vcd");
        }
    }

    tb.runAllTests();

    return tb.tests_failed > 0 ? 1 : 0;
}
