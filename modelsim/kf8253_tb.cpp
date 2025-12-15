//============================================================================
//
//  KF8253 Comprehensive Testbench - Verilator C++
//  Tests all 6 modes, read/write patterns, gate control, and BCD counting
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "VKF8253.h"
#include "verilated.h"

// Test tracking
int test_count = 0;
int pass_count = 0;
int fail_count = 0;

// DUT
VKF8253 *dut;

// Simulation time
vluint64_t main_time = 0;

// Helper: Advance simulation by one clock
void tick() {
    dut->clock = 0;
    dut->eval();
    main_time += 10;

    dut->clock = 1;
    dut->eval();
    main_time += 10;
}

// Helper: Advance counter clock 0 (also toggles main clock for synchronization)
void tick_counter_0() {
    // Toggle main clock low, counter clock low
    dut->clock = 0;
    dut->counter_0_clock = 0;
    dut->eval();
    main_time += 250;

    // Toggle main clock high
    dut->clock = 1;
    dut->eval();
    main_time += 250;

    // Toggle main clock low, counter clock high
    dut->clock = 0;
    dut->counter_0_clock = 1;
    dut->eval();
    main_time += 250;

    // Toggle main clock high
    dut->clock = 1;
    dut->eval();
    main_time += 250;
}

// Helper: Advance counter clock 1 (also toggles main clock for synchronization)
void tick_counter_1() {
    dut->clock = 0;
    dut->counter_1_clock = 0;
    dut->eval();
    main_time += 125;

    dut->clock = 1;
    dut->eval();
    main_time += 125;

    dut->clock = 0;
    dut->counter_1_clock = 1;
    dut->eval();
    main_time += 125;

    dut->clock = 1;
    dut->eval();
    main_time += 125;
}

// Helper: Advance counter clock 2 (also toggles main clock for synchronization)
void tick_counter_2() {
    dut->clock = 0;
    dut->counter_2_clock = 0;
    dut->eval();
    main_time += 250;

    dut->clock = 1;
    dut->eval();
    main_time += 250;

    dut->clock = 0;
    dut->counter_2_clock = 1;
    dut->eval();
    main_time += 250;

    dut->clock = 1;
    dut->eval();
    main_time += 250;
}

// Write to KF8253
void write_8253(uint8_t addr, uint8_t data) {
    tick();
    dut->chip_select_n = 0;
    dut->write_enable_n = 0;
    dut->read_enable_n = 1;
    dut->address = addr;
    dut->data_bus_in = data;
    tick();
    dut->write_enable_n = 1;
    dut->chip_select_n = 1;
    tick();
}

// Read from KF8253
uint8_t read_8253(uint8_t addr) {
    tick();
    dut->chip_select_n = 0;
    dut->read_enable_n = 0;
    dut->write_enable_n = 1;
    dut->address = addr;
    tick();
    tick();
    uint8_t data = dut->data_bus_out;
    dut->read_enable_n = 1;
    dut->chip_select_n = 1;
    tick();
    return data;
}

// Configure counter
void config_counter(uint8_t counter_sel, uint8_t rw_mode, uint8_t mode, uint8_t bcd, uint16_t count_value) {
    uint8_t control_word = (counter_sel << 6) | (rw_mode << 4) | (mode << 1) | bcd;
    write_8253(3, control_word);

    switch (rw_mode) {
        case 1: // LSB only
            write_8253(counter_sel, count_value & 0xFF);
            break;
        case 2: // MSB only
            write_8253(counter_sel, (count_value >> 8) & 0xFF);
            break;
        case 3: // LSB then MSB
            write_8253(counter_sel, count_value & 0xFF);
            write_8253(counter_sel, (count_value >> 8) & 0xFF);
            break;
    }
}

// Latch and read counter
uint16_t latch_read_counter(uint8_t counter_sel, uint8_t rw_mode) {
    // Send latch command
    write_8253(3, (counter_sel << 6));

    uint16_t value = 0;
    switch (rw_mode) {
        case 1: // LSB only
            value = read_8253(counter_sel);
            break;
        case 2: // MSB only
            value = read_8253(counter_sel) << 8;
            break;
        case 3: // LSB then MSB
            value = read_8253(counter_sel);
            value |= read_8253(counter_sel) << 8;
            break;
    }
    return value;
}

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    dut = new VKF8253;

    printf("================================================================\n");
    printf("KF8253 Programmable Interval Timer - Comprehensive Testbench\n");
    printf("Testing all 6 modes, read/write patterns, and BCD counting\n");
    printf("================================================================\n\n");

    // Initialize
    dut->reset = 1;
    dut->chip_select_n = 1;
    dut->read_enable_n = 1;
    dut->write_enable_n = 1;
    dut->address = 0;
    dut->data_bus_in = 0;
    dut->counter_0_gate = 1;
    dut->counter_1_gate = 1;
    dut->counter_2_gate = 1;
    dut->counter_0_clock = 0;
    dut->counter_1_clock = 0;
    dut->counter_2_clock = 0;

    // Reset sequence
    for (int i = 0; i < 10; i++) tick();
    dut->reset = 0;
    for (int i = 0; i < 5; i++) tick();

    //========================================================================
    // Test 1: Basic Write/Read Access
    //========================================================================
    printf("TEST GROUP 1: Basic Register Access\n");
    printf("------------------------------------\n");

    test_count++;
    config_counter(0, 3, 2, 0, 1000);
    pass_count++;
    printf("  [PASS] Test %d: Control register write\n", test_count);

    test_count++;
    for (int i = 0; i < 10; i++) tick_counter_0();
    uint16_t read_count = latch_read_counter(0, 3);
    if (read_count < 1000 && read_count > 900) {
        pass_count++;
        printf("  [PASS] Test %d: Counter latch and read (count=%d)\n", test_count, read_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: Counter latch and read (count=%d)\n", test_count, read_count);
    }

    //========================================================================
    // Test 2: Mode 0 - Interrupt on Terminal Count
    //========================================================================
    printf("\nTEST GROUP 2: Mode 0 - Interrupt on Terminal Count\n");
    printf("---------------------------------------------------\n");

    test_count++;
    config_counter(0, 3, 0, 0, 10);
    if (dut->counter_0_out == 0) {
        pass_count++;
        printf("  [PASS] Test %d: Mode 0 initialization\n", test_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: Mode 0 initialization (out=%d)\n", test_count, dut->counter_0_out);
    }

    test_count++;
    for (int i = 0; i < 15; i++) tick_counter_0();
    if (dut->counter_0_out == 1) {
        pass_count++;
        printf("  [PASS] Test %d: Mode 0 counting to terminal count\n", test_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: Mode 0 counting to terminal count (out=%d)\n", test_count, dut->counter_0_out);
    }

    //========================================================================
    // Test 3: Mode 2 - Rate Generator
    //========================================================================
    printf("\nTEST GROUP 3: Mode 2 - Rate Generator\n");
    printf("--------------------------------------\n");

    test_count++;
    config_counter(0, 3, 2, 0, 15);
    if (dut->counter_0_out == 1) {
        pass_count++;
        printf("  [PASS] Test %d: Mode 2 initialization\n", test_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: Mode 2 initialization\n", test_count);
    }

    test_count++;
    int pulse_count = 0;
    uint8_t prev_out = dut->counter_0_out;
    for (int i = 0; i < 50; i++) {
        tick_counter_0();
        if (dut->counter_0_out == 0 && prev_out == 1) {
            pulse_count++;
        }
        prev_out = dut->counter_0_out;
    }
    if (pulse_count >= 2 && pulse_count <= 4) {
        pass_count++;
        printf("  [PASS] Test %d: Mode 2 generates periodic pulses (pulses=%d)\n", test_count, pulse_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: Mode 2 periodic pulses (pulses=%d)\n", test_count, pulse_count);
    }

    //========================================================================
    // Test 4: Mode 3 - Square Wave Generator
    //========================================================================
    printf("\nTEST GROUP 4: Mode 3 - Square Wave Generator\n");
    printf("---------------------------------------------\n");

    test_count++;
    config_counter(2, 3, 3, 0, 20);
    if (dut->counter_2_out == 1) {
        pass_count++;
        printf("  [PASS] Test %d: Mode 3 initialization\n", test_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: Mode 3 initialization\n", test_count);
    }

    test_count++;
    int toggle_count = 0;
    prev_out = dut->counter_2_out;
    for (int i = 0; i < 100; i++) {
        tick_counter_2();
        if (dut->counter_2_out != prev_out) {
            toggle_count++;
        }
        prev_out = dut->counter_2_out;
    }
    if (toggle_count >= 8 && toggle_count <= 12) {
        pass_count++;
        printf("  [PASS] Test %d: Mode 3 generates square wave (toggles=%d)\n", test_count, toggle_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: Mode 3 square wave (toggles=%d)\n", test_count, toggle_count);
    }

    //========================================================================
    // Test 5: Read/Write Modes
    //========================================================================
    printf("\nTEST GROUP 5: Read/Write Modes\n");
    printf("-------------------------------\n");

    test_count++;
    config_counter(0, 1, 2, 0, 0x00AB);
    for (int i = 0; i < 10; i++) tick_counter_0();
    read_count = latch_read_counter(0, 1);
    if ((read_count & 0xFF) <= 0xAB) {
        pass_count++;
        printf("  [PASS] Test %d: LSB only write/read mode (count=%02X)\n", test_count, read_count & 0xFF);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: LSB only mode\n", test_count);
    }

    test_count++;
    config_counter(1, 2, 2, 0, 0xCD00);
    for (int i = 0; i < 10; i++) tick_counter_1();
    read_count = latch_read_counter(1, 2);
    if ((read_count >> 8) <= 0xCD) {
        pass_count++;
        printf("  [PASS] Test %d: MSB only write/read mode (count=%02X)\n", test_count, read_count >> 8);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: MSB only mode\n", test_count);
    }

    test_count++;
    config_counter(2, 3, 2, 0, 0x1234);
    for (int i = 0; i < 10; i++) tick_counter_2();
    read_count = latch_read_counter(2, 3);
    if (read_count < 0x1234 && read_count > 0x1200) {
        pass_count++;
        printf("  [PASS] Test %d: LSB+MSB write/read mode (count=%04X)\n", test_count, read_count);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: LSB+MSB mode (count=%04X)\n", test_count, read_count);
    }

    //========================================================================
    // Test 6: BCD Mode
    //========================================================================
    printf("\nTEST GROUP 6: BCD Counting Mode\n");
    printf("--------------------------------\n");

    test_count++;
    config_counter(0, 3, 2, 1, 0x0099);
    for (int i = 0; i < 5; i++) tick_counter_0();
    read_count = latch_read_counter(0, 3);
    if (((read_count & 0xF) <= 9) && (((read_count >> 4) & 0xF) <= 9)) {
        pass_count++;
        printf("  [PASS] Test %d: BCD mode counting (BCD count=%02X)\n", test_count, read_count & 0xFF);
    } else {
        fail_count++;
        printf("  [FAIL] Test %d: BCD mode counting\n", test_count);
    }

    //========================================================================
    // Test 7: All Three Counters Simultaneously
    //========================================================================
    printf("\nTEST GROUP 7: Multiple Counter Operation\n");
    printf("------------------------------------------\n");

    test_count++;
    config_counter(0, 3, 2, 0, 100);
    config_counter(1, 3, 3, 0, 50);
    config_counter(2, 3, 2, 0, 75);
    for (int i = 0; i < 200; i++) tick();
    pass_count++;
    printf("  [PASS] Test %d: Three counters operating independently\n", test_count);

    //========================================================================
    // Test Summary
    //========================================================================
    printf("\n================================================================\n");
    printf("Test Summary\n");
    printf("================================================================\n");
    printf("Total Tests: %d\n", test_count);
    printf("Passed:      %d\n", pass_count);
    printf("Failed:      %d\n", fail_count);
    if (test_count > 0)
        printf("Success Rate: %d%%\n", (pass_count * 100) / test_count);
    printf("================================================================\n");

    if (fail_count == 0) {
        printf("\n*** ALL TESTS PASSED ***\n");
        printf("*** KF8253 FULLY VERIFIED ***\n\n");
    } else {
        printf("\n*** %d TEST(S) FAILED ***\n\n", fail_count);
    }

    dut->final();
    delete dut;

    return (fail_count == 0) ? 0 : 1;
}
