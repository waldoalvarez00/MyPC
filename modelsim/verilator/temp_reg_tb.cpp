// ================================================================
// Verilator C++ Testbench for TempReg
// Tests temporary register storage
// ================================================================

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "VTempReg.h"
#include <iostream>
#include <iomanip>
#include <cstdlib>

class TempRegTB {
private:
    VTempReg* dut;
    VerilatedVcdC* tfp;
    uint64_t time_counter;
    int test_count;
    int pass_count;
    int fail_count;

public:
    TempRegTB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VTempReg;
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open("temp_reg_tb.vcd");

        // Initialize inputs
        dut->clk = 0;
        dut->reset = 1;
        dut->wr_val = 0;
        dut->wr_en = 0;
    }

    ~TempRegTB() {
        tfp->close();
        delete tfp;
        delete dut;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        tfp->dump(time_counter++);

        dut->clk = 1;
        dut->eval();
        tfp->dump(time_counter++);
    }

    void reset_dut() {
        dut->reset = 1;
        for (int i = 0; i < 3; i++) tick();
        dut->reset = 0;
        for (int i = 0; i < 2; i++) tick();
    }

    void check_result(const char* test_name, uint16_t expected) {
        test_count++;
        if (dut->val == expected) {
            std::cout << "[PASS] Test " << test_count << ": " << test_name
                      << " (val=0x" << std::hex << std::setw(4) << std::setfill('0')
                      << dut->val << ")" << std::dec << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] Test " << test_count << ": " << test_name
                      << " (expected 0x" << std::hex << std::setw(4) << std::setfill('0')
                      << expected << ", got 0x" << std::setw(4) << dut->val
                      << ")" << std::dec << std::endl;
            fail_count++;
        }
    }

    void run_tests() {
        std::cout << "================================================================" << std::endl;
        std::cout << "TempReg Unit Test (Verilator)" << std::endl;
        std::cout << "================================================================" << std::endl << std::endl;

        reset_dut();

        // ================================================================
        // TEST 1: Reset State
        // ================================================================
        std::cout << "--- Test 1: Reset State ---" << std::endl;

        check_result("Value after reset", 0x0000);

        // ================================================================
        // TEST 2: Write Value
        // ================================================================
        std::cout << std::endl << "--- Test 2: Write Value ---" << std::endl;

        dut->wr_val = 0x1234;
        dut->wr_en = 1;
        tick();
        dut->wr_en = 0;
        tick();

        check_result("After write 0x1234", 0x1234);

        // ================================================================
        // TEST 3: Write Another Value
        // ================================================================
        std::cout << std::endl << "--- Test 3: Overwrite ---" << std::endl;

        dut->wr_val = 0x5678;
        dut->wr_en = 1;
        tick();
        dut->wr_en = 0;
        tick();

        check_result("After write 0x5678", 0x5678);

        // ================================================================
        // TEST 4: Write Without Enable
        // ================================================================
        std::cout << std::endl << "--- Test 4: Write Without Enable ---" << std::endl;

        dut->wr_val = 0xFFFF;
        dut->wr_en = 0;  // Write disabled
        tick();
        tick();

        check_result("Value unchanged without wr_en", 0x5678);

        // ================================================================
        // TEST 5: Multiple Writes
        // ================================================================
        std::cout << std::endl << "--- Test 5: Sequential Writes ---" << std::endl;

        dut->wr_en = 1;
        for (int i = 0; i < 5; i++) {
            dut->wr_val = 0x1000 + i;
            tick();
        }
        dut->wr_en = 0;
        tick();

        check_result("Last value written", 0x1004);

        // ================================================================
        // TEST 6: Write All Zeros
        // ================================================================
        std::cout << std::endl << "--- Test 6: Write Zeros ---" << std::endl;

        dut->wr_val = 0x0000;
        dut->wr_en = 1;
        tick();
        dut->wr_en = 0;
        tick();

        check_result("Write all zeros", 0x0000);

        // ================================================================
        // TEST 7: Write All Ones
        // ================================================================
        std::cout << std::endl << "--- Test 7: Write All Ones ---" << std::endl;

        dut->wr_val = 0xFFFF;
        dut->wr_en = 1;
        tick();
        dut->wr_en = 0;
        tick();

        check_result("Write all ones", 0xFFFF);

        // ================================================================
        // TEST 8: Reset During Operation
        // ================================================================
        std::cout << std::endl << "--- Test 8: Reset During Operation ---" << std::endl;

        dut->wr_val = 0xABCD;
        dut->wr_en = 1;
        tick();

        dut->reset = 1;
        tick();
        dut->reset = 0;
        dut->wr_en = 0;
        tick();

        check_result("Value reset to zero", 0x0000);

        // ================================================================
        // TEST 9: Value Retention
        // ================================================================
        std::cout << std::endl << "--- Test 9: Value Retention ---" << std::endl;

        dut->wr_val = 0x9876;
        dut->wr_en = 1;
        tick();
        dut->wr_en = 0;

        // Wait many cycles
        for (int i = 0; i < 10; i++) tick();

        check_result("Value retained after many cycles", 0x9876);

        // ================================================================
        // TEST 10: Pattern Test
        // ================================================================
        std::cout << std::endl << "--- Test 10: Bit Patterns ---" << std::endl;

        // Test walking 1s
        dut->wr_en = 1;
        dut->wr_val = 0x0001;
        tick();
        dut->wr_en = 0;
        tick();
        check_result("Pattern 0x0001", 0x0001);

        dut->wr_en = 1;
        dut->wr_val = 0x8000;
        tick();
        dut->wr_en = 0;
        tick();
        check_result("Pattern 0x8000", 0x8000);

        dut->wr_en = 1;
        dut->wr_val = 0xAAAA;
        tick();
        dut->wr_en = 0;
        tick();
        check_result("Pattern 0xAAAA", 0xAAAA);

        dut->wr_en = 1;
        dut->wr_val = 0x5555;
        tick();
        dut->wr_en = 0;
        tick();
        check_result("Pattern 0x5555", 0x5555);

        // ================================================================
        // Summary
        // ================================================================
        std::cout << std::endl << "================================================================" << std::endl;
        std::cout << "TEST SUMMARY" << std::endl;
        std::cout << "================================================================" << std::endl;
        std::cout << "Total Tests: " << test_count << std::endl;
        std::cout << "Passed:      " << pass_count << std::endl;
        std::cout << "Failed:      " << fail_count << std::endl;
        std::cout << "Pass Rate:   " << (test_count > 0 ? (pass_count * 100) / test_count : 0) << "%" << std::endl;
        std::cout << "================================================================" << std::endl;

        if (fail_count == 0) {
            std::cout << "✓✓✓ ALL TESTS PASSED ✓✓✓" << std::endl << std::endl;
        } else {
            std::cout << "✗✗✗ SOME TESTS FAILED ✗✗✗" << std::endl << std::endl;
        }
    }

    int get_exit_code() {
        return (fail_count == 0) ? 0 : 1;
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    TempRegTB* tb = new TempRegTB();
    tb->run_tests();
    int exit_code = tb->get_exit_code();
    delete tb;

    return exit_code;
}
