// ================================================================
// Verilator C++ Testbench for SegmentRegisterFile
// Tests segment register read/write operations and CS port
// ================================================================

#include "VSegmentRegisterFile.h"
#include "verilated.h"
#include <iostream>
#include <iomanip>

// Segment register indices (from RegisterEnum.sv)
#define ES 0
#define CS 1
#define SS 2
#define DS 3

class SegmentRegisterFileTB {
private:
    VSegmentRegisterFile* dut;
    unsigned long long time_counter;
    int test_count;
    int pass_count;
    int fail_count;

public:
    SegmentRegisterFileTB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VSegmentRegisterFile;
        dut->clk = 0;
        dut->reset = 0;
        dut->rd_sel = 0;
        dut->wr_en = 0;
        dut->wr_sel = 0;
        dut->wr_val = 0;
    }

    ~SegmentRegisterFileTB() {
        dut->final();
        delete dut;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        time_counter++;

        dut->clk = 1;
        dut->eval();
        time_counter++;
    }

    void reset_dut() {
        dut->reset = 1;
        tick();
        tick();
        dut->reset = 0;
        tick();
    }

    void check_result(const char* test_name, bool condition, uint16_t expected = 0, uint16_t actual = 0) {
        test_count++;
        if (condition) {
            std::cout << "[PASS] Test " << test_count << ": " << test_name << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] Test " << test_count << ": " << test_name;
            if (expected != 0 || actual != 0) {
                std::cout << " (expected 0x" << std::hex << std::setfill('0') << std::setw(4)
                         << expected << ", got 0x" << actual << std::dec << ")";
            }
            std::cout << std::endl;
            fail_count++;
        }
    }

    void write_segment(uint8_t sel, uint16_t val) {
        dut->wr_sel = sel;
        dut->wr_val = val;
        dut->wr_en = 1;
        tick();
        dut->wr_en = 0;
        tick();
    }

    uint16_t read_segment(uint8_t sel) {
        dut->rd_sel = sel;
        tick();
        tick(); // Read latency
        return dut->rd_val;
    }

    void run_tests() {
        std::cout << "================================================================" << std::endl;
        std::cout << "SegmentRegisterFile Unit Test (Verilator)" << std::endl;
        std::cout << "================================================================" << std::endl << std::endl;

        // Initialize
        tick();
        tick();
        tick();

        // ================================================================
        // TEST 1: Write and Read Back ES
        // ================================================================
        std::cout << "--- Test 1: Write and Read ES ---" << std::endl;
        write_segment(ES, 0x1234);
        uint16_t es_val = read_segment(ES);
        check_result("ES write/read", es_val == 0x1234, 0x1234, es_val);

        // ================================================================
        // TEST 2: Write and Read Back CS
        // ================================================================
        std::cout << std::endl << "--- Test 2: Write and Read CS ---" << std::endl;
        write_segment(CS, 0x5678);
        uint16_t cs_val = read_segment(CS);
        check_result("CS write/read", cs_val == 0x5678, 0x5678, cs_val);
        check_result("CS port output", dut->cs == 0x5678, 0x5678, dut->cs);

        // ================================================================
        // TEST 3: Write and Read Back SS
        // ================================================================
        std::cout << std::endl << "--- Test 3: Write and Read SS ---" << std::endl;
        write_segment(SS, 0x9ABC);
        uint16_t ss_val = read_segment(SS);
        check_result("SS write/read", ss_val == 0x9ABC, 0x9ABC, ss_val);

        // ================================================================
        // TEST 4: Write and Read Back DS
        // ================================================================
        std::cout << std::endl << "--- Test 4: Write and Read DS ---" << std::endl;
        write_segment(DS, 0xDEF0);
        uint16_t ds_val = read_segment(DS);
        check_result("DS write/read", ds_val == 0xDEF0, 0xDEF0, ds_val);

        // ================================================================
        // TEST 5: Read Bypass (Write and Read Simultaneously)
        // ================================================================
        std::cout << std::endl << "--- Test 5: Read Bypass ---" << std::endl;
        dut->wr_sel = ES;
        dut->wr_val = 0xABCD;
        dut->wr_en = 1;
        dut->rd_sel = ES;
        tick();
        tick();
        check_result("Read bypass", dut->rd_val == 0xABCD, 0xABCD, dut->rd_val);
        dut->wr_en = 0;
        tick();

        // ================================================================
        // TEST 6: Multiple Writes to Same Register
        // ================================================================
        std::cout << std::endl << "--- Test 6: Multiple Writes ---" << std::endl;
        dut->wr_sel = CS;
        dut->wr_en = 1;
        dut->wr_val = 0x1111;
        tick();
        dut->wr_val = 0x2222;
        tick();
        dut->wr_val = 0x3333;
        tick();
        dut->wr_en = 0;
        dut->rd_sel = CS;
        tick();
        tick();
        check_result("Multiple writes (last value wins)", dut->rd_val == 0x3333, 0x3333, dut->rd_val);
        check_result("CS port tracks writes", dut->cs == 0x3333, 0x3333, dut->cs);

        // ================================================================
        // TEST 7: Write Without Enable
        // ================================================================
        std::cout << std::endl << "--- Test 7: Write Without Enable ---" << std::endl;
        dut->rd_sel = DS;
        tick();
        tick();
        uint16_t original_ds = dut->rd_val;

        dut->wr_sel = DS;
        dut->wr_val = 0xFFFF;
        dut->wr_en = 0;  // Write disabled
        tick();

        dut->rd_sel = DS;
        tick();
        tick();
        check_result("Write without enable (no change)", dut->rd_val == original_ds, original_ds, dut->rd_val);

        // ================================================================
        // TEST 8: Independent Register Storage
        // ================================================================
        std::cout << std::endl << "--- Test 8: Independent Registers ---" << std::endl;

        // Write unique values to all registers
        dut->wr_en = 1;
        dut->wr_sel = ES; dut->wr_val = 0x00E5; tick();
        dut->wr_sel = CS; dut->wr_val = 0x00C5; tick();
        dut->wr_sel = SS; dut->wr_val = 0x0055; tick();
        dut->wr_sel = DS; dut->wr_val = 0x00D5; tick();
        dut->wr_en = 0;

        // Read back and verify all
        check_result("ES independent", read_segment(ES) == 0x00E5);
        check_result("CS independent", read_segment(CS) == 0x00C5);
        check_result("SS independent", read_segment(SS) == 0x0055);
        check_result("DS independent", read_segment(DS) == 0x00D5);

        // ================================================================
        // TEST 9: CS Port Always Reflects CS Register
        // ================================================================
        std::cout << std::endl << "--- Test 9: CS Port Tracking ---" << std::endl;
        dut->wr_sel = CS;
        dut->wr_en = 1;
        dut->wr_val = 0xAAAA;
        tick();
        check_result("CS port updates immediately (AAAA)", dut->cs == 0xAAAA);

        dut->wr_val = 0x5555;
        tick();
        check_result("CS port updates immediately (5555)", dut->cs == 0x5555);
        dut->wr_en = 0;
        tick();

        // ================================================================
        // TEST 10: Back-to-Back Reads from Different Registers
        // ================================================================
        std::cout << std::endl << "--- Test 10: Back-to-Back Reads ---" << std::endl;
        uint16_t es_read = read_segment(ES);
        uint16_t ds_read = read_segment(DS);
        check_result("Back-to-back ES read", es_read == 0x00E5, 0x00E5, es_read);
        check_result("Back-to-back DS read", ds_read == 0x00D5, 0x00D5, ds_read);

        // ================================================================
        // Summary
        // ================================================================
        std::cout << std::endl << "================================================================" << std::endl;
        std::cout << "TEST SUMMARY" << std::endl;
        std::cout << "================================================================" << std::endl;
        std::cout << "Total Tests: " << test_count << std::endl;
        std::cout << "Passed:      " << pass_count << std::endl;
        std::cout << "Failed:      " << fail_count << std::endl;
        if (test_count > 0)
            std::cout << "Pass Rate:   " << (pass_count * 100 / test_count) << "%" << std::endl;
        std::cout << "================================================================" << std::endl;

        if (fail_count == 0) {
            std::cout << "✓✓✓ ALL TESTS PASSED ✓✓✓" << std::endl << std::endl;
        } else {
            std::cout << "✗✗✗ SOME TESTS FAILED ✗✗✗" << std::endl << std::endl;
        }
    }

    int get_fail_count() const { return fail_count; }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    SegmentRegisterFileTB tb;
    tb.run_tests();

    return (tb.get_fail_count() > 0) ? 1 : 0;
}
