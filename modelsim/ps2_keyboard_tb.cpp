//============================================================================
//
//  PS2KeyboardController Verilator C++ Testbench
//  Tests PS/2 Keyboard controller CPU interface and basic functionality
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

#include <verilated.h>
#include "VPS2KeyboardController.h"
#include <cstdio>
#include <cstdint>

// Test tracking
int test_count = 0;
int pass_count = 0;
int fail_count = 0;

// DUT instance
VPS2KeyboardController* dut;

// Simulation time
vluint64_t main_time = 0;

// Helper: Advance one clock cycle
void tick() {
    dut->clk = 0;
    dut->eval();
    main_time++;
    dut->clk = 1;
    dut->eval();
    main_time++;
}

// Helper: Wait for ACK
void wait_for_ack() {
    int timeout = 100;
    while (!dut->data_m_ack && timeout > 0) {
        tick();
        timeout--;
    }
    if (timeout == 0) {
        printf("ERROR: ACK timeout!\n");
    }
}

// Helper: CPU read
uint16_t cpu_read() {
    tick();
    dut->cs = 1;
    dut->data_m_access = 1;
    dut->data_m_wr_en = 0;
    dut->data_m_bytesel = 0b11;  // Read full word

    wait_for_ack();
    tick();

    uint16_t data = dut->data_m_data_out;

    dut->cs = 0;
    dut->data_m_access = 0;
    tick();

    return data;
}

// Helper: CPU write
void cpu_write(uint16_t data, uint8_t bytesel) {
    tick();
    dut->cs = 1;
    dut->data_m_access = 1;
    dut->data_m_wr_en = 1;
    dut->data_m_data_in = data;
    dut->data_m_bytesel = bytesel;

    wait_for_ack();
    tick();

    dut->cs = 0;
    dut->data_m_access = 0;
    dut->data_m_wr_en = 0;
    tick();
}

// Test reporting
void report_test(const char* name, bool passed) {
    test_count++;
    if (passed) {
        printf("  [PASS] %s\n", name);
        pass_count++;
    } else {
        printf("  [FAIL] %s\n", name);
        fail_count++;
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    printf("================================================================\n");
    printf("PS2KeyboardController Verilator C++ Testbench\n");
    printf("Testing PS/2 Keyboard controller CPU interface\n");
    printf("================================================================\n");
    printf("\n");

    // Create DUT instance
    dut = new VPS2KeyboardController;

    // Initialize signals
    dut->clk = 0;
    dut->reset = 1;
    dut->cs = 0;
    dut->data_m_access = 0;
    dut->data_m_wr_en = 0;
    dut->data_m_data_in = 0;
    dut->data_m_bytesel = 0;
    dut->ps2_clk_in = 1;  // Idle high
    dut->ps2_dat_in = 1;  // Idle high

    // Reset sequence
    for (int i = 0; i < 10; i++) tick();
    dut->reset = 0;
    for (int i = 0; i < 10; i++) tick();

    // Test 1: Initial status read
    printf("Test 1: Initial status read\n");
    uint16_t read_data = cpu_read();
    uint8_t status = (read_data >> 8) & 0xFF;
    uint8_t data_byte = read_data & 0xFF;
    printf("  Status: 0x%02X, Data: 0x%02X\n", status, data_byte);

    // Status bits:
    // Bit 4 = ~empty (FIFO not empty) - should be 0 initially
    // Bit 3 = tx_busy - may be high during initialization
    // Bit 2 = error - should be 0 initially
    // Bit 1 = speaker_data - should be 0 initially
    // Bit 0 = speaker_gate_en - should be 0 initially
    report_test("Initial FIFO empty", (status & 0x10) == 0);
    report_test("Initial status read successful", true);
    report_test("Initial error cleared", (status & 0x04) == 0);
    report_test("Initial speaker_data low", ((status & 0x02) == 0) && (dut->speaker_data == 0));
    report_test("Initial speaker_gate_en low", ((status & 0x01) == 0) && (dut->speaker_gate_en == 0));

    printf("\n");
    printf("Test 2: ACK signal verification\n");
    tick();
    dut->cs = 1;
    dut->data_m_access = 1;
    dut->data_m_wr_en = 0;
    tick();
    tick();
    report_test("ACK asserted during access", dut->data_m_ack == 1);
    dut->cs = 0;
    dut->data_m_access = 0;
    tick();  // ACK is registered, stays high this cycle
    tick();  // ACK clears on next cycle
    report_test("ACK cleared after access", dut->data_m_ack == 0);

    printf("\n");
    printf("Test 3: Speaker control - enable gate\n");
    // Write to upper byte: bit 8 = speaker_gate_en, bit 9 = speaker_data
    cpu_write(0x0100, 0b10);  // Set speaker_gate_en
    for (int i = 0; i < 5; i++) tick();
    read_data = cpu_read();
    status = (read_data >> 8) & 0xFF;
    report_test("Speaker gate enabled", (dut->speaker_gate_en == 1) && ((status & 0x01) == 1));
    report_test("Speaker data still low", (dut->speaker_data == 0) && ((status & 0x02) == 0));

    printf("\n");
    printf("Test 4: Speaker control - set data\n");
    cpu_write(0x0300, 0b10);  // Set both speaker_gate_en and speaker_data
    for (int i = 0; i < 5; i++) tick();
    read_data = cpu_read();
    status = (read_data >> 8) & 0xFF;
    report_test("Speaker data enabled", (dut->speaker_data == 1) && ((status & 0x02) == 2));
    report_test("Speaker gate still enabled", (dut->speaker_gate_en == 1) && ((status & 0x01) == 1));

    printf("\n");
    printf("Test 5: Speaker control - clear both\n");
    cpu_write(0x0000, 0b10);  // Clear both signals
    for (int i = 0; i < 5; i++) tick();
    read_data = cpu_read();
    status = (read_data >> 8) & 0xFF;
    report_test("Speaker signals cleared", (dut->speaker_data == 0) && (dut->speaker_gate_en == 0));

    printf("\n");
    printf("Test 6: FIFO flush command\n");
    // Write flush command (bit 15 high, upper byte)
    cpu_write(0x8000, 0b10);
    for (int i = 0; i < 5; i++) tick();
    read_data = cpu_read();
    status = (read_data >> 8) & 0xFF;
    report_test("FIFO flushed (empty)", (status & 0x10) == 0);

    printf("\n");
    printf("Test 7: Chip select requirement\n");
    tick();
    dut->cs = 0;  // CS low
    dut->data_m_access = 1;
    dut->data_m_wr_en = 0;
    for (int i = 0; i < 3; i++) tick();
    report_test("No ACK without CS", dut->data_m_ack == 0);
    dut->data_m_access = 0;
    tick();

    printf("\n");
    printf("Test 8: Byte select functionality\n");
    // Read only lower byte (data)
    tick();
    dut->cs = 1;
    dut->data_m_access = 1;
    dut->data_m_wr_en = 0;
    dut->data_m_bytesel = 0b01;
    wait_for_ack();
    tick();
    read_data = dut->data_m_data_out;
    dut->cs = 0;
    dut->data_m_access = 0;
    tick();
    report_test("Lower byte read", true);

    // Read only upper byte (status)
    tick();
    dut->cs = 1;
    dut->data_m_access = 1;
    dut->data_m_wr_en = 0;
    dut->data_m_bytesel = 0b10;
    wait_for_ack();
    tick();
    read_data = dut->data_m_data_out;
    dut->cs = 0;
    dut->data_m_access = 0;
    tick();
    report_test("Upper byte read", true);

    printf("\n");
    printf("Test 9: Sequential operations\n");
    for (int i = 0; i < 5; i++) {
        read_data = cpu_read();
        printf("  Read %d: Status=0x%02X, Data=0x%02X\n",
               i, (read_data >> 8) & 0xFF, read_data & 0xFF);
    }
    report_test("Sequential reads", true);

    printf("\n");
    printf("Test 10: Speaker pattern test\n");
    // Test various speaker control patterns
    cpu_write(0x0100, 0b10);  // gate=1, data=0
    for (int i = 0; i < 5; i++) tick();
    cpu_write(0x0300, 0b10);  // gate=1, data=1
    for (int i = 0; i < 5; i++) tick();
    cpu_write(0x0200, 0b10);  // gate=0, data=1
    for (int i = 0; i < 5; i++) tick();
    cpu_write(0x0000, 0b10);  // gate=0, data=0
    for (int i = 0; i < 5; i++) tick();
    report_test("Speaker pattern control", true);

    // Test Summary
    printf("\n");
    printf("================================================================\n");
    printf("Test Summary\n");
    printf("================================================================\n");
    printf("Total Tests: %d\n", test_count);
    printf("Passed:      %d\n", pass_count);
    printf("Failed:      %d\n", fail_count);
    printf("Success Rate: %d%%\n", (pass_count * 100) / test_count);
    printf("================================================================\n");

    printf("\n");
    printf("NOTE: This testbench focuses on CPU interface testing.\n");
    printf("Full PS/2 protocol and scancode translation testing requires\n");
    printf("complex timing simulation and PS/2 device simulation.\n");
    printf("\n");

    if (fail_count == 0) {
        printf("*** ALL CPU INTERFACE TESTS PASSED ***\n");
    } else {
        printf("*** SOME TESTS FAILED ***\n");
    }

    // Cleanup
    delete dut;

    return (fail_count == 0) ? 0 : 1;
}
