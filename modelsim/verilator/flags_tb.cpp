// ================================================================
// Verilator C++ Testbench for Flags Module
// Tests CPU flags register (C, P, A, Z, S, T, I, D, O)
// ================================================================

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "VFlags_verilator.h"
#include <iostream>
#include <iomanip>
#include <cstdlib>

// Flag indices in 16-bit register
#define CF_IDX 0
#define PF_IDX 2
#define AF_IDX 4
#define ZF_IDX 6
#define SF_IDX 7
#define TF_IDX 8
#define IF_IDX 9
#define DF_IDX 10
#define OF_IDX 11

// Update flags bit positions (9-bit mask)
#define UpdateFlags_CF 0
#define UpdateFlags_PF 1
#define UpdateFlags_AF 2
#define UpdateFlags_ZF 3
#define UpdateFlags_SF 4
#define UpdateFlags_TF 5
#define UpdateFlags_IF 6
#define UpdateFlags_DF 7
#define UpdateFlags_OF 8

class FlagsTB {
private:
    VFlags_verilator* dut;
    VerilatedVcdC* tfp;
    unsigned long long time_counter;
    int test_count;
    int pass_count;
    int fail_count;

public:
    FlagsTB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VFlags_verilator;
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open("flags_tb.vcd");

        // Initialize inputs
        dut->clk = 0;
        dut->reset = 1;
        dut->flags_in = 0;
        dut->update_flags = 0;
    }

    ~FlagsTB() {
        tfp->close();
        delete tfp;
        delete dut;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        tfp->dump(static_cast<uint64_t>(time_counter++));

        dut->clk = 1;
        dut->eval();
        tfp->dump(static_cast<uint64_t>(time_counter++));
    }

    void reset_dut() {
        dut->reset = 1;
        for (int i = 0; i < 3; i++) tick();
        dut->reset = 0;
        for (int i = 0; i < 2; i++) tick();
    }

    void check_flag(const char* flag_name, int flag_idx, bool expected) {
        test_count++;
        bool actual = (dut->flags_out >> flag_idx) & 1;
        if (actual == expected) {
            std::cout << "[PASS] Test " << test_count << ": " << flag_name
                      << " = " << (int)expected << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] Test " << test_count << ": " << flag_name
                      << " (expected " << (int)expected << ", got " << (int)actual << ")" << std::endl;
            fail_count++;
        }
    }

    void check_result(const char* test_name, bool condition) {
        test_count++;
        if (condition) {
            std::cout << "[PASS] Test " << test_count << ": " << test_name << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] Test " << test_count << ": " << test_name << std::endl;
            std::cout << "        Expected condition to be true, but was false" << std::endl;
            std::cout << "        flags_out = 0x" << std::hex << std::setw(4)
                      << std::setfill('0') << dut->flags_out << std::dec << std::endl;
            fail_count++;
        }
    }

    void run_tests() {
        std::cout << "================================================================" << std::endl;
        std::cout << "Flags Module Unit Test (Verilator)" << std::endl;
        std::cout << "================================================================" << std::endl << std::endl;

        reset_dut();

        // ================================================================
        // TEST 1: Reset State
        // ================================================================
        std::cout << "--- Test 1: Reset State ---" << std::endl;

        check_flag("CF after reset", CF_IDX, false);
        check_flag("PF after reset", PF_IDX, false);
        check_flag("AF after reset", AF_IDX, false);
        check_flag("ZF after reset", ZF_IDX, false);
        check_flag("SF after reset", SF_IDX, false);
        check_flag("TF after reset", TF_IDX, false);
        check_flag("IF after reset", IF_IDX, false);
        check_flag("DF after reset", DF_IDX, false);
        check_flag("OF after reset", OF_IDX, false);

        // ================================================================
        // TEST 2: Set Carry Flag
        // ================================================================
        std::cout << std::endl << "--- Test 2: Set Carry Flag ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << CF_IDX);
        dut->update_flags = (1 << UpdateFlags_CF);
        tick();
        tick();

        check_flag("CF set", CF_IDX, true);
        check_flag("Other flags unchanged (PF)", PF_IDX, false);

        // ================================================================
        // TEST 3: Set Zero Flag
        // ================================================================
        std::cout << std::endl << "--- Test 3: Set Zero Flag ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << ZF_IDX);
        dut->update_flags = (1 << UpdateFlags_ZF);
        tick();
        tick();

        check_flag("ZF set", ZF_IDX, true);
        check_flag("CF still set from previous test", CF_IDX, true);

        // ================================================================
        // TEST 4: Set Sign Flag
        // ================================================================
        std::cout << std::endl << "--- Test 4: Set Sign Flag ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << SF_IDX);
        dut->update_flags = (1 << UpdateFlags_SF);
        tick();
        tick();

        check_flag("SF set", SF_IDX, true);

        // ================================================================
        // TEST 5: Set Overflow Flag
        // ================================================================
        std::cout << std::endl << "--- Test 5: Set Overflow Flag ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << OF_IDX);
        dut->update_flags = (1 << UpdateFlags_OF);
        tick();
        tick();

        check_flag("OF set", OF_IDX, true);

        // ================================================================
        // TEST 6: Set Parity Flag
        // ================================================================
        std::cout << std::endl << "--- Test 6: Set Parity Flag ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << PF_IDX);
        dut->update_flags = (1 << UpdateFlags_PF);
        tick();
        tick();

        check_flag("PF set", PF_IDX, true);

        // ================================================================
        // TEST 7: Set Auxiliary Carry Flag
        // ================================================================
        std::cout << std::endl << "--- Test 7: Set Auxiliary Carry ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << AF_IDX);
        dut->update_flags = (1 << UpdateFlags_AF);
        tick();
        tick();

        check_flag("AF set", AF_IDX, true);

        // ================================================================
        // TEST 8: Set Trap Flag (for single-step debugging)
        // ================================================================
        std::cout << std::endl << "--- Test 8: Set Trap Flag ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << TF_IDX);
        dut->update_flags = (1 << UpdateFlags_TF);
        tick();
        tick();

        check_flag("TF set", TF_IDX, true);

        // ================================================================
        // TEST 9: Set Interrupt Enable Flag
        // ================================================================
        std::cout << std::endl << "--- Test 9: Set Interrupt Enable ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << IF_IDX);
        dut->update_flags = (1 << UpdateFlags_IF);
        tick();
        tick();

        check_flag("IF set", IF_IDX, true);

        // ================================================================
        // TEST 10: Set Direction Flag
        // ================================================================
        std::cout << std::endl << "--- Test 10: Set Direction Flag ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << DF_IDX);
        dut->update_flags = (1 << UpdateFlags_DF);
        tick();
        tick();

        check_flag("DF set", DF_IDX, true);

        // ================================================================
        // TEST 11: Clear Flags
        // ================================================================
        std::cout << std::endl << "--- Test 11: Clear Flags ---" << std::endl;

        dut->flags_in = 0;  // All zeros
        dut->update_flags = (1 << UpdateFlags_CF) | (1 << UpdateFlags_ZF) | (1 << UpdateFlags_SF);
        tick();
        tick();

        check_flag("CF cleared", CF_IDX, false);
        check_flag("ZF cleared", ZF_IDX, false);
        check_flag("SF cleared", SF_IDX, false);

        // ================================================================
        // TEST 12: Update Multiple Flags Simultaneously
        // ================================================================
        std::cout << std::endl << "--- Test 12: Multiple Flag Update ---" << std::endl;

        dut->flags_in = 0;
        dut->flags_in |= (1 << CF_IDX);
        dut->flags_in |= (1 << ZF_IDX);
        dut->flags_in |= (1 << OF_IDX);
        dut->flags_in |= (1 << SF_IDX);
        dut->update_flags = (1 << UpdateFlags_CF) | (1 << UpdateFlags_ZF) |
                            (1 << UpdateFlags_OF) | (1 << UpdateFlags_SF);
        tick();
        tick();

        check_flag("CF in multi-update", CF_IDX, true);
        check_flag("ZF in multi-update", ZF_IDX, true);
        check_flag("OF in multi-update", OF_IDX, true);
        check_flag("SF in multi-update", SF_IDX, true);

        // ================================================================
        // TEST 13: Selective Flag Preservation
        // ================================================================
        std::cout << std::endl << "--- Test 13: Selective Preservation ---" << std::endl;

        // Set all flags
        dut->flags_in = 0xFFFF;
        dut->update_flags = 0x1FF;  // Update all
        tick();
        tick();

        // Now update only CF, others should be preserved
        dut->flags_in = 0;  // Try to clear all
        dut->flags_in &= ~(1 << CF_IDX);  // CF = 0
        dut->update_flags = (1 << UpdateFlags_CF);  // Only update CF
        tick();
        tick();

        check_flag("CF updated to 0", CF_IDX, false);
        check_flag("ZF preserved as 1", ZF_IDX, true);
        check_flag("SF preserved as 1", SF_IDX, true);
        check_flag("OF preserved as 1", OF_IDX, true);

        // ================================================================
        // TEST 14: No Update When update_flags is 0
        // ================================================================
        std::cout << std::endl << "--- Test 14: No Update ---" << std::endl;

        uint16_t before_flags = dut->flags_out;
        dut->flags_in = 0;  // Try to clear all
        dut->update_flags = 0;  // But don't update anything
        tick();
        tick();

        check_result("Flags unchanged when update=0", dut->flags_out == before_flags);

        // ================================================================
        // TEST 15: Flag Format (x86 compatibility)
        // ================================================================
        std::cout << std::endl << "--- Test 15: Flag Format ---" << std::endl;

        // Set all flags to 1
        dut->flags_in = 0xFFFF;
        dut->update_flags = 0x1FF;
        tick();
        tick();

        // Check format: {4'b0000, O, D, I, T, S, Z, 1'b0, A, 1'b0, P, 1'b1, C}
        check_result("Bit 1 always 1 (reserved)", (dut->flags_out & (1 << 1)) != 0);
        check_result("Bit 3 always 0 (reserved)", (dut->flags_out & (1 << 3)) == 0);
        check_result("Bit 5 always 0 (reserved)", (dut->flags_out & (1 << 5)) == 0);

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

    FlagsTB* tb = new FlagsTB();
    tb->run_tests();
    int exit_code = tb->get_exit_code();
    delete tb;

    return exit_code;
}
