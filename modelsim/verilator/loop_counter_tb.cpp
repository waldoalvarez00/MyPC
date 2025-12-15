// ================================================================
// Verilator C++ Testbench for LoopCounter
// Tests microcode loop counter functionality
// ================================================================

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "VLoopCounter.h"
#include <iostream>
#include <iomanip>
#include <cstdlib>

class LoopCounterTB {
private:
    VLoopCounter* dut;
    VerilatedVcdC* tfp;
    uint64_t time_counter;
    int test_count;
    int pass_count;
    int fail_count;

public:
    LoopCounterTB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VLoopCounter;
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open("loop_counter_tb.vcd");

        // Initialize inputs
        dut->clk = 0;
        dut->count_in = 0;
        dut->load = 0;
        dut->next = 0;
    }

    ~LoopCounterTB() {
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

    void check_result(const char* test_name, bool condition) {
        test_count++;
        if (condition) {
            std::cout << "[PASS] Test " << test_count << ": " << test_name << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] Test " << test_count << ": " << test_name
                      << " (done=" << (int)dut->done << ")" << std::endl;
            fail_count++;
        }
    }

    void run_tests() {
        std::cout << "================================================================" << std::endl;
        std::cout << "LoopCounter Unit Test (Verilator)" << std::endl;
        std::cout << "================================================================" << std::endl << std::endl;

        // Initialize
        for (int i = 0; i < 3; i++) tick();

        // ================================================================
        // TEST 1: Initial State (done should be true for count=0)
        // ================================================================
        std::cout << "--- Test 1: Initial State ---" << std::endl;

        check_result("Done true when count=0", dut->done == 1);

        // ================================================================
        // TEST 2: Load Count
        // ================================================================
        std::cout << std::endl << "--- Test 2: Load Count ---" << std::endl;

        dut->count_in = 5;
        dut->load = 1;
        tick();
        dut->load = 0;
        tick();

        check_result("Done false after loading 5", dut->done == 0);

        // ================================================================
        // TEST 3: Decrement Counter
        // ================================================================
        std::cout << std::endl << "--- Test 3: Decrement ---" << std::endl;

        dut->next = 1;
        tick();  // count = 4
        check_result("After 1st decrement, done=0", dut->done == 0);

        tick();  // count = 3
        check_result("After 2nd decrement, done=0", dut->done == 0);

        tick();  // count = 2
        check_result("After 3rd decrement, done=0", dut->done == 0);

        tick();  // count = 1
        check_result("After 4th decrement, done=0", dut->done == 0);

        tick();  // count = 0
        dut->next = 0;
        tick();
        check_result("After 5th decrement, done=1", dut->done == 1);

        // ================================================================
        // TEST 4: Load While Counting
        // ================================================================
        std::cout << std::endl << "--- Test 4: Reload During Count ---" << std::endl;

        dut->count_in = 3;
        dut->load = 1;
        tick();
        dut->load = 0;
        tick();

        dut->next = 1;
        tick();  // count = 2

        // Reload with new value
        dut->count_in = 10;
        dut->load = 1;
        tick();
        dut->load = 0;
        dut->next = 0;
        tick();

        check_result("Reloaded count, done=0", dut->done == 0);

        // ================================================================
        // TEST 5: Count Down to Zero
        // ================================================================
        std::cout << std::endl << "--- Test 5: Full Countdown ---" << std::endl;

        dut->count_in = 3;
        dut->load = 1;
        tick();
        dut->load = 0;
        dut->next = 1;

        tick();  // 2
        tick();  // 1
        tick();  // 0
        dut->next = 0;
        tick();

        check_result("Full countdown complete", dut->done == 1);

        // ================================================================
        // TEST 6: Load Zero
        // ================================================================
        std::cout << std::endl << "--- Test 6: Load Zero ---" << std::endl;

        dut->count_in = 0;
        dut->load = 1;
        tick();
        dut->load = 0;
        tick();

        check_result("Loaded zero, done=1", dut->done == 1);

        // ================================================================
        // TEST 7: Load Maximum Value
        // ================================================================
        std::cout << std::endl << "--- Test 7: Load Maximum ---" << std::endl;

        dut->count_in = 31;  // Maximum 5-bit value
        dut->load = 1;
        tick();
        dut->load = 0;
        tick();

        check_result("Loaded max value, done=0", dut->done == 0);

        // Decrement a few times
        dut->next = 1;
        for (int i = 0; i < 5; i++) {
            tick();
        }
        dut->next = 0;
        tick();

        check_result("After partial countdown, done=0", dut->done == 0);

        // ================================================================
        // TEST 8: Next Without Load
        // ================================================================
        std::cout << std::endl << "--- Test 8: Next Without Load ---" << std::endl;

        // Ensure counter is at zero
        dut->count_in = 0;
        dut->load = 1;
        tick();
        dut->load = 0;
        tick();

        // Try to decrement when already at zero
        dut->next = 1;
        tick();
        tick();
        dut->next = 0;
        tick();

        check_result("Next at zero doesn't underflow", dut->done == 1);

        // ================================================================
        // TEST 9: Rapid Load/Next
        // ================================================================
        std::cout << std::endl << "--- Test 9: Rapid Operations ---" << std::endl;

        dut->count_in = 2;
        dut->load = 1;
        dut->next = 1;  // Both signals high
        tick();
        dut->load = 0;
        tick();  // Decrement
        tick();  // Decrement to 0
        dut->next = 0;
        tick();

        check_result("Rapid load/next operations", dut->done == 1);

        // ================================================================
        // TEST 10: Single Count
        // ================================================================
        std::cout << std::endl << "--- Test 10: Single Count ---" << std::endl;

        dut->count_in = 1;
        dut->load = 1;
        tick();
        dut->load = 0;
        tick();

        check_result("Loaded 1, done=0", dut->done == 0);

        dut->next = 1;
        tick();  // Decrement to 0
        dut->next = 0;
        tick();

        check_result("After single decrement, done=1", dut->done == 1);

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

    LoopCounterTB* tb = new LoopCounterTB();
    tb->run_tests();
    int exit_code = tb->get_exit_code();
    delete tb;

    return exit_code;
}
