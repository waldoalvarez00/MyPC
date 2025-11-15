// ================================================================
// Verilator C++ Testbench for IP (Instruction Pointer)
// Tests IP increment, rollback, and write operations
// ================================================================

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "VIP.h"
#include <iostream>
#include <iomanip>
#include <cstdlib>

class IP_TB {
private:
    VIP* dut;
    VerilatedVcdC* tfp;
    uint64_t time_counter;
    int test_count;
    int pass_count;
    int fail_count;

public:
    IP_TB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VIP;
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open("ip_tb.vcd");

        // Initialize inputs
        dut->clk = 0;
        dut->reset = 1;
        dut->start_instruction = 0;
        dut->next_instruction = 0;
        dut->rollback = 0;
        dut->inc = 0;
        dut->wr_en = 0;
        dut->wr_val = 0;
    }

    ~IP_TB() {
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
                      << " (IP=0x" << std::hex << std::setw(4) << std::setfill('0')
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
        std::cout << "IP (Instruction Pointer) Unit Test (Verilator)" << std::endl;
        std::cout << "================================================================" << std::endl << std::endl;

        reset_dut();

        // ================================================================
        // TEST 1: Reset State
        // ================================================================
        std::cout << "--- Test 1: Reset State ---" << std::endl;
        check_result("IP after reset", 0x0000);

        // ================================================================
        // TEST 2: Direct Write to IP
        // ================================================================
        std::cout << std::endl << "--- Test 2: Direct Write ---" << std::endl;

        dut->wr_en = 1;
        dut->wr_val = 0x1234;
        tick();
        dut->wr_en = 0;
        tick();

        check_result("IP after write", 0x1234);

        // ================================================================
        // TEST 3: Increment IP (start_instruction)
        // ================================================================
        std::cout << std::endl << "--- Test 3: Increment on Start Instruction ---" << std::endl;

        // Set IP to known value
        dut->wr_en = 1;
        dut->wr_val = 0x0100;
        tick();
        dut->wr_en = 0;
        tick();

        // Increment by 1
        dut->start_instruction = 1;
        dut->inc = 1;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("IP after inc by 1", 0x0101);

        // ================================================================
        // TEST 4: Increment IP by Various Amounts
        // ================================================================
        std::cout << std::endl << "--- Test 4: Various Increments ---" << std::endl;

        // Increment by 2
        dut->start_instruction = 1;
        dut->inc = 2;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("IP after inc by 2", 0x0103);

        // Increment by 5
        dut->start_instruction = 1;
        dut->inc = 5;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("IP after inc by 5", 0x0108);

        // ================================================================
        // TEST 5: Rollback to Instruction Start
        // ================================================================
        std::cout << std::endl << "--- Test 5: Rollback ---" << std::endl;

        // Set IP and mark instruction start
        dut->wr_en = 1;
        dut->wr_val = 0x0200;
        tick();
        dut->wr_en = 0;

        dut->start_instruction = 1;
        dut->inc = 0;
        tick();
        dut->start_instruction = 0;
        tick();

        // Increment IP several times
        dut->start_instruction = 1;
        dut->inc = 3;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("IP before rollback", 0x0203);

        // Rollback to instruction start
        dut->rollback = 1;
        tick();
        dut->rollback = 0;
        tick();

        check_result("IP after rollback", 0x0200);

        // ================================================================
        // TEST 6: Next Instruction
        // ================================================================
        std::cout << std::endl << "--- Test 6: Next Instruction ---" << std::endl;

        // Set IP
        dut->wr_en = 1;
        dut->wr_val = 0x0300;
        tick();
        dut->wr_en = 0;
        tick();

        // Mark as instruction start
        dut->next_instruction = 1;
        tick();
        dut->next_instruction = 0;
        tick();

        // Increment
        dut->start_instruction = 1;
        dut->inc = 4;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("IP after increment", 0x0304);

        // Rollback should go to 0x0300
        dut->rollback = 1;
        tick();
        dut->rollback = 0;
        tick();

        check_result("Rollback to instruction start", 0x0300);

        // ================================================================
        // TEST 7: Write Overrides Increment
        // ================================================================
        std::cout << std::endl << "--- Test 7: Write vs Increment Priority ---" << std::endl;

        dut->wr_en = 1;
        dut->wr_val = 0x0500;
        dut->start_instruction = 1;
        dut->inc = 10;
        tick();
        dut->wr_en = 0;
        dut->start_instruction = 0;
        tick();

        check_result("Write takes priority over increment", 0x0500);

        // ================================================================
        // TEST 8: Wrap Around (16-bit overflow)
        // ================================================================
        std::cout << std::endl << "--- Test 8: 16-bit Wrap Around ---" << std::endl;

        dut->wr_en = 1;
        dut->wr_val = 0xFFFE;
        tick();
        dut->wr_en = 0;
        tick();

        dut->start_instruction = 1;
        dut->inc = 5;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("16-bit wrap around", 0x0003);

        // ================================================================
        // TEST 9: Multiple Start Instructions
        // ================================================================
        std::cout << std::endl << "--- Test 9: Sequential Increments ---" << std::endl;

        dut->wr_en = 1;
        dut->wr_val = 0x1000;
        tick();
        dut->wr_en = 0;
        tick();

        // Series of increments
        for (int i = 0; i < 5; i++) {
            dut->start_instruction = 1;
            dut->inc = 1;
            tick();
            dut->start_instruction = 0;
            tick();
        }

        check_result("After 5 increments of 1", 0x1005);

        // ================================================================
        // TEST 10: Instruction Start Address Tracking
        // ================================================================
        std::cout << std::endl << "--- Test 10: Instruction Start Tracking ---" << std::endl;

        // Write initial value
        dut->wr_en = 1;
        dut->wr_val = 0x2000;
        dut->next_instruction = 1;
        tick();
        dut->wr_en = 0;
        dut->next_instruction = 0;
        tick();

        // Increment multiple times
        dut->start_instruction = 1;
        dut->inc = 2;
        tick();
        dut->start_instruction = 0;
        tick();

        dut->start_instruction = 1;
        dut->inc = 3;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("After increments", 0x2005);

        // Rollback should go to 0x2002 (last start_instruction updated the address)
        // Note: start_instruction updates instruction_start_addr each time
        dut->rollback = 1;
        tick();
        dut->rollback = 0;
        tick();

        check_result("Rollback to last start addr", 0x2002);

        // ================================================================
        // TEST 11: Zero Increment
        // ================================================================
        std::cout << std::endl << "--- Test 11: Zero Increment ---" << std::endl;

        dut->wr_en = 1;
        dut->wr_val = 0x3000;
        tick();
        dut->wr_en = 0;
        tick();

        dut->start_instruction = 1;
        dut->inc = 0;
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("Zero increment (no change)", 0x3000);

        // ================================================================
        // TEST 12: Maximum Increment
        // ================================================================
        std::cout << std::endl << "--- Test 12: Maximum Increment ---" << std::endl;

        dut->wr_en = 1;
        dut->wr_val = 0x4000;
        tick();
        dut->wr_en = 0;
        tick();

        dut->start_instruction = 1;
        dut->inc = 15;  // Maximum 4-bit value
        tick();
        dut->start_instruction = 0;
        tick();

        check_result("Maximum increment (15)", 0x400F);

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

    IP_TB* tb = new IP_TB();
    tb->run_tests();
    int exit_code = tb->get_exit_code();
    delete tb;

    return exit_code;
}
