// C++ testbench for Divider module using Verilator
// Tests DIV/IDIV instructions (8-bit and 16-bit, signed and unsigned)

#include <verilated.h>
#include "VDivider.h"
#include <iostream>
#include <cstdlib>

using namespace std;

// Test tracking
int test_num = 0;
int errors = 0;
int passed_tests = 0;

// DUT
VDivider* dut;

// Simulation time
vluint64_t main_time = 0;

// Called by $time in Verilog
double sc_time_stamp() {
    return main_time;
}

// Clock cycle
void tick() {
    dut->clk = 0;
    dut->eval();
    main_time++;
    dut->clk = 1;
    dut->eval();
    main_time++;
}

// Reset the DUT
void reset() {
    dut->reset = 1;
    for (int i = 0; i < 5; i++) tick();
    dut->reset = 0;
    for (int i = 0; i < 2; i++) tick();
}

// Perform division and wait for completion
void do_divide(uint32_t dividend, uint16_t divisor, bool is_8bit, bool is_signed) {
    dut->dividend = dividend;
    dut->divisor = divisor;
    dut->is_8_bit = is_8bit ? 1 : 0;
    dut->is_signed = is_signed ? 1 : 0;
    dut->eval();  // Evaluate combinational logic
    dut->start = 1;
    dut->eval();  // Evaluate combinational logic again
    tick();

    // Check for immediate error (division by zero, overflow)
    // Error/complete are set on this clock edge if raise_error is true
    bool immediate_error = (dut->error != 0);

    tick();  // Extra tick to let error/complete propagate
    dut->start = 0;

    // If immediate error, we're done
    if (immediate_error) {
        tick();
        return;
    }

    // Wait for completion or error (max 50 cycles)
    for (int i = 0; i < 50; i++) {
        tick();
        if (dut->complete || dut->error)
            break;
    }

    // Extra cycle for stability
    tick();
}

// Test 1: 8-bit unsigned: 100 / 5 = 20, rem 0
void test_1_8bit_unsigned_simple() {
    test_num++;
    cout << "\nTest " << test_num << ": 8-bit unsigned division (100 / 5)" << endl;

    do_divide(100, 5, true, false);

    uint8_t quotient_8 = dut->quotient & 0xFF;
    uint8_t remainder_8 = dut->remainder & 0xFF;

    if (!dut->error && quotient_8 == 20 && remainder_8 == 0) {
        cout << "  ✓ Result correct: Q=" << (int)quotient_8 << ", R=" << (int)remainder_8 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=20, R=0; Got Q=" << (int)quotient_8
             << ", R=" << (int)remainder_8 << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 2: 8-bit unsigned: 101 / 5 = 20, rem 1
void test_2_8bit_unsigned_remainder() {
    test_num++;
    cout << "\nTest " << test_num << ": 8-bit unsigned division with remainder (101 / 5)" << endl;

    do_divide(101, 5, true, false);

    uint8_t quotient_8 = dut->quotient & 0xFF;
    uint8_t remainder_8 = dut->remainder & 0xFF;

    if (!dut->error && quotient_8 == 20 && remainder_8 == 1) {
        cout << "  ✓ Result correct: Q=" << (int)quotient_8 << ", R=" << (int)remainder_8 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=20, R=1; Got Q=" << (int)quotient_8
             << ", R=" << (int)remainder_8 << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 3: 16-bit unsigned: 10000 / 100 = 100, rem 0
void test_3_16bit_unsigned_simple() {
    test_num++;
    cout << "\nTest " << test_num << ": 16-bit unsigned division (10000 / 100)" << endl;

    do_divide(10000, 100, false, false);

    if (!dut->error && dut->quotient == 100 && dut->remainder == 0) {
        cout << "  ✓ Result correct: Q=" << dut->quotient << ", R=" << dut->remainder << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=100, R=0; Got Q=" << dut->quotient
             << ", R=" << dut->remainder << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 4: 16-bit unsigned: 12345 / 100 = 123, rem 45
void test_4_16bit_unsigned_remainder() {
    test_num++;
    cout << "\nTest " << test_num << ": 16-bit unsigned division with remainder (12345 / 100)" << endl;

    do_divide(12345, 100, false, false);

    if (!dut->error && dut->quotient == 123 && dut->remainder == 45) {
        cout << "  ✓ Result correct: Q=" << dut->quotient << ", R=" << dut->remainder << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=123, R=45; Got Q=" << dut->quotient
             << ", R=" << dut->remainder << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 5: 8-bit signed: 100 / 5 = 20, rem 0 (both positive)
void test_5_8bit_signed_pos_pos() {
    test_num++;
    cout << "\nTest " << test_num << ": 8-bit signed division +100 / +5" << endl;

    do_divide(100, 5, true, true);

    int8_t quotient_8 = dut->quotient & 0xFF;
    int8_t remainder_8 = dut->remainder & 0xFF;

    if (!dut->error && quotient_8 == 20 && remainder_8 == 0) {
        cout << "  ✓ Result correct: Q=" << (int)quotient_8 << ", R=" << (int)remainder_8 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=20, R=0; Got Q=" << (int)quotient_8
             << ", R=" << (int)remainder_8 << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 6: 8-bit signed: 100 / -5 = -20 (positive / negative)
void test_6_8bit_signed_pos_neg() {
    test_num++;
    cout << "\nTest " << test_num << ": 8-bit signed division +100 / -5" << endl;

    do_divide(100, 0xFFFB, true, true);  // -5 in 16-bit two's complement

    int8_t quotient_8 = dut->quotient & 0xFF;

    if (!dut->error && quotient_8 == -20) {
        cout << "  ✓ Result correct: Q=" << (int)quotient_8 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=-20; Got Q=" << (int)quotient_8
             << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 7: 8-bit signed: -100 / 5 = -20 (negative / positive)
void test_7_8bit_signed_neg_pos() {
    test_num++;
    cout << "\nTest " << test_num << ": 8-bit signed division -100 / +5" << endl;

    do_divide(0xFFFFFF9C, 5, true, true);  // -100 in 32-bit

    int8_t quotient_8 = dut->quotient & 0xFF;

    if (!dut->error && quotient_8 == -20) {
        cout << "  ✓ Result correct: Q=" << (int)quotient_8 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=-20; Got Q=" << (int)quotient_8
             << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 8: 8-bit signed: -100 / -5 = 20 (negative / negative)
void test_8_8bit_signed_neg_neg() {
    test_num++;
    cout << "\nTest " << test_num << ": 8-bit signed division -100 / -5" << endl;

    do_divide(0xFFFFFF9C, 0xFFFB, true, true);

    int8_t quotient_8 = dut->quotient & 0xFF;

    if (!dut->error && quotient_8 == 20) {
        cout << "  ✓ Result correct: Q=" << (int)quotient_8 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=20; Got Q=" << (int)quotient_8
             << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 9: 16-bit signed: 1000 / 10 = 100 (both positive)
void test_9_16bit_signed_pos_pos() {
    test_num++;
    cout << "\nTest " << test_num << ": 16-bit signed division +1000 / +10" << endl;

    do_divide(1000, 10, false, true);

    int16_t quotient_16 = dut->quotient;
    int16_t remainder_16 = dut->remainder;

    if (!dut->error && quotient_16 == 100 && remainder_16 == 0) {
        cout << "  ✓ Result correct: Q=" << quotient_16 << ", R=" << remainder_16 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=100, R=0; Got Q=" << quotient_16
             << ", R=" << remainder_16 << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 10: 16-bit signed: -1000 / 10 = -100 (mixed signs)
void test_10_16bit_signed_mixed() {
    test_num++;
    cout << "\nTest " << test_num << ": 16-bit signed division -1000 / +10" << endl;

    do_divide(0xFFFFFC18, 10, false, true);  // -1000 in 32-bit

    int16_t quotient_16 = dut->quotient;

    if (!dut->error && quotient_16 == -100) {
        cout << "  ✓ Result correct: Q=" << quotient_16 << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=-100; Got Q=" << quotient_16
             << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 11: Division by zero
void test_11_divide_by_zero() {
    test_num++;
    cout << "\nTest " << test_num << ": Division by zero (100 / 0)" << endl;

    do_divide(100, 0, false, false);

    cout << "  DEBUG: error=" << (int)dut->error << ", complete=" << (int)dut->complete << endl;

    if (dut->error) {
        cout << "  ✓ Error correctly raised for division by zero" << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected error flag, got error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 12: Overflow condition
void test_12_overflow() {
    test_num++;
    cout << "\nTest " << test_num << ": Overflow condition (65535 / 1)" << endl;

    do_divide(0x0000FF00, 1, true, false);

    cout << "  DEBUG: error=" << (int)dut->error << ", complete=" << (int)dut->complete << endl;

    if (dut->error) {
        cout << "  ✓ Overflow correctly detected" << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected overflow error, got error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 13: Divide by 1
void test_13_divide_by_one() {
    test_num++;
    cout << "\nTest " << test_num << ": Divide by 1 (123 / 1)" << endl;

    do_divide(123, 1, false, false);

    if (!dut->error && dut->quotient == 123 && dut->remainder == 0) {
        cout << "  ✓ Result correct: Q=" << dut->quotient << ", R=" << dut->remainder << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=123, R=0; Got Q=" << dut->quotient
             << ", R=" << dut->remainder << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

// Test 14: Dividend smaller than divisor
void test_14_dividend_smaller() {
    test_num++;
    cout << "\nTest " << test_num << ": Dividend < divisor (5 / 10)" << endl;

    do_divide(5, 10, false, false);

    if (!dut->error && dut->quotient == 0 && dut->remainder == 5) {
        cout << "  ✓ Result correct: Q=" << dut->quotient << ", R=" << dut->remainder << endl;
        passed_tests++;
    } else {
        cout << "  ✗ FAILED: Expected Q=0, R=5; Got Q=" << dut->quotient
             << ", R=" << dut->remainder << ", error=" << (int)dut->error << endl;
        errors++;
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    cout << "========================================" << endl;
    cout << "Divider Unit Test (Verilator)" << endl;
    cout << "========================================" << endl;

    // Create DUT
    dut = new VDivider;

    // Initialize signals
    dut->reset = 1;
    dut->start = 0;
    dut->is_8_bit = 0;
    dut->is_signed = 0;
    dut->dividend = 0;
    dut->divisor = 0;
    dut->clk = 0;

    // Reset
    reset();

    // Run tests
    test_1_8bit_unsigned_simple();
    test_2_8bit_unsigned_remainder();
    test_3_16bit_unsigned_simple();
    test_4_16bit_unsigned_remainder();
    test_5_8bit_signed_pos_pos();
    test_6_8bit_signed_pos_neg();
    test_7_8bit_signed_neg_pos();
    test_8_8bit_signed_neg_neg();
    test_9_16bit_signed_pos_pos();
    test_10_16bit_signed_mixed();
    test_11_divide_by_zero();
    test_12_overflow();
    test_13_divide_by_one();
    test_14_dividend_smaller();

    // Final results
    cout << "\n========================================" << endl;
    cout << "Test Summary:" << endl;
    cout << "  Total Tests: " << test_num << endl;
    cout << "  Passed:      " << passed_tests << endl;
    cout << "  Failed:      " << errors << endl;
    cout << "========================================" << endl;

    if (errors == 0)
        cout << "✓ ALL TESTS PASSED" << endl;
    else
        cout << "✗ SOME TESTS FAILED" << endl;

    // Cleanup
    dut->final();
    delete dut;

    return errors > 0 ? 1 : 0;
}
