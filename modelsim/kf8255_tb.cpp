//============================================================================
//
//  KF8255 (8255 PPI) Verilator C++ Testbench
//  Comprehensive test coverage for Programmable Peripheral Interface
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

#include <verilated.h>
#include "VKF8255.h"
#include <iostream>
#include <iomanip>
#include <string>

using namespace std;

// Test tracking
int test_count = 0;
int pass_count = 0;
int fail_count = 0;

// DUT pointer
VKF8255* dut = nullptr;
vluint64_t main_time = 0;

// Helper function to advance time
void tick() {
    dut->clock = 0;
    dut->eval();
    main_time++;

    dut->clock = 1;
    dut->eval();
    main_time++;
}

// Write to PPI
void write_ppi(uint8_t addr, uint8_t data) {
    dut->chip_select = 1;
    dut->write_enable = 1;
    dut->read_enable = 0;
    dut->address = addr & 0x3;
    dut->data_bus_in = data;
    tick();

    dut->write_enable = 0;
    tick();

    dut->chip_select = 0;
    tick();
}

// Read from PPI
uint8_t read_ppi(uint8_t addr) {
    dut->chip_select = 1;
    dut->write_enable = 0;
    dut->read_enable = 1;
    dut->address = addr & 0x3;
    tick();
    tick();

    uint8_t data = dut->data_bus_out;

    dut->chip_select = 0;
    dut->read_enable = 0;
    tick();

    return data;
}

// Test helper
void run_test(const string& name, bool condition) {
    test_count++;
    if (condition) {
        cout << "  [PASS] " << name << endl;
        pass_count++;
    } else {
        cout << "  [FAIL] " << name << endl;
        fail_count++;
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    dut = new VKF8255;

    cout << "================================================================" << endl;
    cout << "KF8255 (8255 PPI) Verilator C++ Testbench" << endl;
    cout << "Testing Programmable Peripheral Interface for PC compatibility" << endl;
    cout << "================================================================" << endl;
    cout << endl;

    // Initialize
    dut->reset = 1;
    dut->chip_select = 0;
    dut->read_enable = 0;
    dut->write_enable = 0;
    dut->address = 0;
    dut->data_bus_in = 0;
    dut->port_a_in = 0;
    dut->port_b_in = 0;
    dut->port_c_in = 0;

    // Reset sequence
    for (int i = 0; i < 10; i++) tick();
    dut->reset = 0;
    for (int i = 0; i < 5; i++) tick();

    // Test 1: Configure Mode 0 - All ports as outputs
    cout << "Test 1: Configure Mode 0 - All ports as outputs" << endl;
    write_ppi(0x3, 0x80);  // Control word: all outputs
    for (int i = 0; i < 5; i++) tick();

    run_test("Mode 0 configured, ports set as outputs",
             dut->port_a_io == 0 && dut->port_b_io == 0);

    // Test 2: Write to Port A and verify output
    cout << endl << "Test 2: Write to Port A and verify output" << endl;
    write_ppi(0x0, 0xAA);
    for (int i = 0; i < 5; i++) tick();

    run_test("Port A output = 0xAA", dut->port_a_out == 0xAA);

    // Test 3: Write to Port B and verify output
    cout << endl << "Test 3: Write to Port B and verify output" << endl;
    write_ppi(0x1, 0x55);
    for (int i = 0; i < 5; i++) tick();

    run_test("Port B output = 0x55", dut->port_b_out == 0x55);

    // Test 4: Write to Port C and verify output
    cout << endl << "Test 4: Write to Port C and verify output" << endl;
    write_ppi(0x2, 0xF0);
    for (int i = 0; i < 5; i++) tick();

    run_test("Port C output = 0xF0", dut->port_c_out == 0xF0);

    // Test 5: Configure Mode 0 - All ports as inputs
    cout << endl << "Test 5: Configure Mode 0 - All ports as inputs" << endl;
    write_ppi(0x3, 0x9B);  // Control word: all inputs
    for (int i = 0; i < 5; i++) tick();

    run_test("Ports configured as inputs",
             dut->port_a_io == 1 && dut->port_b_io == 1);

    // Test 6: Read from Port A (input mode)
    cout << endl << "Test 6: Read from Port A (input mode)" << endl;
    dut->port_a_in = 0x3C;
    for (int i = 0; i < 5; i++) tick();
    uint8_t read_data = read_ppi(0x0);

    run_test("Port A read = 0x3C", read_data == 0x3C);

    // Test 7: Read from Port B (input mode)
    cout << endl << "Test 7: Read from Port B (input mode)" << endl;
    dut->port_b_in = 0xC3;
    for (int i = 0; i < 5; i++) tick();
    read_data = read_ppi(0x1);

    run_test("Port B read = 0xC3", read_data == 0xC3);

    // Test 8: Read from Port C (input mode)
    cout << endl << "Test 8: Read from Port C (input mode)" << endl;
    dut->port_c_in = 0x0F;
    for (int i = 0; i < 5; i++) tick();
    read_data = read_ppi(0x2);

    run_test("Port C read = 0x0F", read_data == 0x0F);

    // Test 9: Port C bit set/reset (BSR mode)
    cout << endl << "Test 9: Port C bit set/reset (BSR mode)" << endl;
    write_ppi(0x3, 0x80);  // All outputs
    write_ppi(0x2, 0x00);  // Clear Port C
    for (int i = 0; i < 5; i++) tick();

    // BSR: Set bit 3
    write_ppi(0x3, 0x07);
    for (int i = 0; i < 5; i++) tick();

    run_test("Port C bit 3 set via BSR", (dut->port_c_out & 0x08) != 0);

    // Test 10: Port C bit reset via BSR
    cout << endl << "Test 10: Port C bit reset via BSR" << endl;
    write_ppi(0x3, 0x06);  // Reset bit 3
    for (int i = 0; i < 5; i++) tick();

    run_test("Port C bit 3 cleared via BSR", (dut->port_c_out & 0x08) == 0);

    // Test 11: Mixed I/O configuration
    cout << endl << "Test 11: Mixed I/O configuration - Port A input, Port B output" << endl;
    write_ppi(0x3, 0x92);  // Port A input, Port B output
    for (int i = 0; i < 5; i++) tick();

    write_ppi(0x1, 0xBB);  // Write to Port B
    dut->port_a_in = 0x77;
    for (int i = 0; i < 5; i++) tick();

    read_data = read_ppi(0x0);

    run_test("Mixed I/O: Port A input=0x77, Port B output=0xBB",
             read_data == 0x77 && dut->port_b_out == 0xBB);

    // Test 12: Verify ACK signal generation
    cout << endl << "Test 12: Verify ACK signal generation" << endl;
    dut->chip_select = 1;
    dut->read_enable = 1;
    dut->address = 0;
    tick();

    run_test("ACK signal asserted on read", dut->ack != 0);

    dut->chip_select = 0;
    dut->read_enable = 0;
    tick();

    // Test 13: PC/XT keyboard interface simulation
    cout << endl << "Test 13: PC/XT keyboard interface simulation" << endl;
    cout << "  [INFO] PC/XT PPI Usage:" << endl;
    cout << "    Port A: Keyboard scancode input" << endl;
    cout << "    Port B: System control (speaker, etc.)" << endl;
    cout << "    Port C: Keyboard control/status" << endl;

    write_ppi(0x3, 0x99);  // Port A in, B out, C mixed
    dut->port_a_in = 0x1E;  // Scancode for 'A' key
    for (int i = 0; i < 5; i++) tick();

    read_data = read_ppi(0x0);

    run_test("Keyboard scancode read correctly (0x1E)", read_data == 0x1E);

    // Test 14: PC speaker control simulation
    cout << endl << "Test 14: PC speaker control simulation (Port B bit 1)" << endl;
    write_ppi(0x1, 0x03);  // Enable speaker
    for (int i = 0; i < 5; i++) tick();

    run_test("Speaker enable bit set (Port B = 0x03)",
             (dut->port_b_out & 0x02) != 0);

    // Test 15: Multiple rapid writes
    cout << endl << "Test 15: Multiple rapid writes" << endl;
    write_ppi(0x0, 0x11);
    write_ppi(0x0, 0x22);
    write_ppi(0x0, 0x33);
    write_ppi(0x0, 0xFF);
    for (int i = 0; i < 5; i++) tick();

    run_test("Rapid writes handled correctly (final value = 0xFF)",
             dut->port_a_out == 0xFF);

    // Test 16: All Port C bits BSR test
    cout << endl << "Test 16: All Port C bits BSR test" << endl;
    write_ppi(0x3, 0x80);  // Port C as output
    write_ppi(0x2, 0x00);  // Clear all

    bool bit_test_pass = true;
    for (int bit = 0; bit < 8; bit++) {
        // Set bit
        write_ppi(0x3, (bit << 1) | 0x01);
        for (int i = 0; i < 3; i++) tick();
        if ((dut->port_c_out & (1 << bit)) == 0) {
            bit_test_pass = false;
            cout << "    [FAIL] Bit " << bit << " set failed" << endl;
        }

        // Clear bit
        write_ppi(0x3, (bit << 1) | 0x00);
        for (int i = 0; i < 3; i++) tick();
        if ((dut->port_c_out & (1 << bit)) != 0) {
            bit_test_pass = false;
            cout << "    [FAIL] Bit " << bit << " clear failed" << endl;
        }
    }

    run_test("All Port C BSR operations successful", bit_test_pass);

    // Test 17: PC compatibility check
    cout << endl << "Test 17: PC compatibility check" << endl;
    cout << "  [INFO] Standard PC PPI configuration:" << endl;
    cout << "    I/O Ports: 0x60-0x63" << endl;
    cout << "    0x60: Port A - Keyboard data" << endl;
    cout << "    0x61: Port B - System control" << endl;
    cout << "    0x62: Port C - Keyboard/system status" << endl;
    cout << "    0x63: Control register" << endl;

    write_ppi(0x3, 0x99);  // Standard PC configuration
    for (int i = 0; i < 5; i++) tick();

    run_test("Standard PC PPI configuration successful",
             dut->port_a_io == 1 && dut->port_b_io == 0);

    // Test Summary
    cout << endl;
    cout << "================================================================" << endl;
    cout << "Test Summary" << endl;
    cout << "================================================================" << endl;
    cout << "Total Tests: " << test_count << endl;
    cout << "Passed:      " << pass_count << endl;
    cout << "Failed:      " << fail_count << endl;
    cout << "Success Rate: " << (pass_count * 100 / test_count) << "%" << endl;
    cout << "================================================================" << endl;

    if (fail_count == 0) {
        cout << endl;
        cout << "*** ALL TESTS PASSED ***" << endl;
        cout << "*** PC PPI COMPATIBILITY VERIFIED ***" << endl;
        cout << endl;
    } else {
        cout << endl;
        cout << "*** SOME TESTS FAILED ***" << endl;
        cout << endl;
    }

    // Cleanup
    delete dut;
    return (fail_count == 0) ? 0 : 1;
}
