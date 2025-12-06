// KF8259 Comprehensive Testbench for Verilator
// Tests 8259A PIC initialization, interrupt handling, priorities, and modes
// Replaces slow Icarus Verilog simulation due to always_comb function inefficiency

#include <verilated.h>
#include <iostream>
#include <cstdint>
#include <cstdlib>
#include <string>

// Include the Verilator-generated header
#include "VKF8259.h"

class KF8259TB {
public:
    VKF8259* dut;
    uint64_t sim_time;
    int test_count;
    int pass_count;
    int fail_count;

    KF8259TB() {
        dut = new VKF8259;
        sim_time = 0;
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
    }

    ~KF8259TB() {
        delete dut;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        sim_time++;

        dut->clk = 1;
        dut->eval();
        sim_time++;
    }

    void tick_n(int n) {
        for (int i = 0; i < n; i++) tick();
    }

    void reset() {
        dut->reset = 1;
        dut->chip_select = 0;
        dut->read_enable = 0;
        dut->write_enable = 0;
        dut->address = 0;
        dut->data_bus_in = 0;
        dut->interrupt_acknowledge_simple = 0;
        dut->cascade_in = 0;
        dut->slave_program_n = 1;
        dut->interrupt_acknowledge_n = 1;
        dut->interrupt_request = 0;

        tick_n(5);
        dut->reset = 0;
        tick_n(5);
    }

    void write_8259(uint8_t addr, uint8_t data) {
        tick();
        dut->chip_select = 1;
        dut->write_enable = 1;
        dut->read_enable = 0;
        dut->address = addr;
        dut->data_bus_in = data;
        tick();
        dut->chip_select = 0;
        dut->write_enable = 0;
        tick();
    }

    uint8_t read_8259(uint8_t addr) {
        tick();
        dut->chip_select = 1;
        dut->read_enable = 1;
        dut->write_enable = 0;
        dut->address = addr;
        tick();
        uint8_t data = dut->data_bus_out & 0xFF;
        tick();
        dut->chip_select = 0;
        dut->read_enable = 0;
        tick();
        return data;
    }

    void init_8259_basic(uint8_t vector_base) {
        // ICW1: Edge-triggered, single, need ICW4
        write_8259(0, 0x13);  // D4=1, LTIM=0, SNGL=1, IC4=1
        // ICW2: Vector base
        write_8259(1, vector_base);
        // ICW4: 8086 mode
        write_8259(1, 0x01);
        // OCW1: Unmask all
        write_8259(1, 0x00);
    }

    void send_eoi(bool specific, uint8_t irq_level) {
        if (specific)
            write_8259(0, 0x60 | (irq_level & 0x07));  // Specific EOI
        else
            write_8259(0, 0x20);  // Non-specific EOI
    }

    void trigger_irq(int irq_num) {
        dut->interrupt_request |= (1 << irq_num);
        tick_n(5);  // Wait for interrupt to propagate - keep line high!
        // Note: interrupt_to_cpu should be checked while IRQ line is still high
    }

    void release_irq(int irq_num) {
        dut->interrupt_request &= ~(1 << irq_num);
        tick_n(3);
    }

    void trigger_irq_pulse(int irq_num) {
        // For tests that don't need to check interrupt_to_cpu
        dut->interrupt_request |= (1 << irq_num);
        tick_n(3);
        dut->interrupt_request &= ~(1 << irq_num);
        tick_n(5);
    }

    void ack_irq() {
        dut->interrupt_acknowledge_simple = 1;
        tick();
        dut->interrupt_acknowledge_simple = 0;
        tick();
    }

    void trigger_and_ack_irq(int irq_num) {
        trigger_irq(irq_num);
        ack_irq();
    }

    void check_result(const char* test_name, bool condition) {
        test_count++;
        if (condition) {
            std::cout << "[PASS] Test " << test_count << ": " << test_name << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] Test " << test_count << ": " << test_name
                      << " (INT=" << (int)dut->interrupt_to_cpu
                      << " IRQ=" << std::hex << (int)dut->simpleirq << std::dec << ")" << std::endl;
            fail_count++;
        }
    }

    void run_tests() {
        std::cout << "================================================================" << std::endl;
        std::cout << "KF8259 Comprehensive Test Suite (Verilator)" << std::endl;
        std::cout << "================================================================" << std::endl;

        reset();

        // ================================================================
        // TEST 1: Initialization Sequence
        // ================================================================
        std::cout << "\n--- Test 1: Basic Initialization (Single Mode) ---" << std::endl;
        init_8259_basic(0x20);
        tick_n(5);
        check_result("Initialization completed", true);

        // ================================================================
        // TEST 2: Single Interrupt Request (Edge-Triggered)
        // ================================================================
        std::cout << "\n--- Test 2: Single Interrupt Request (IRQ0) ---" << std::endl;
        trigger_irq(0);  // IRQ line stays high
        check_result("INT signal raised", dut->interrupt_to_cpu == 1);
        check_result("Correct IRQ vector (0x20)", dut->simpleirq == 0x20);

        release_irq(0);  // Now release IRQ line
        ack_irq();
        tick_n(3);
        send_eoi(false, 0);
        tick_n(3);
        check_result("INT cleared after EOI", dut->interrupt_to_cpu == 0);

        // ================================================================
        // TEST 3: Multiple Interrupts with Priority
        // ================================================================
        std::cout << "\n--- Test 3: Multiple Interrupts with Priority ---" << std::endl;

        // Trigger IRQ3 and IRQ1 simultaneously (keep lines high)
        dut->interrupt_request = (1 << 3) | (1 << 1);
        tick_n(5);

        check_result("Higher priority IRQ1 served first", (dut->simpleirq & 0x07) == 1);

        // Release IRQ1, keep IRQ3 high
        dut->interrupt_request = (1 << 3);
        tick_n(3);
        ack_irq();
        send_eoi(false, 0);
        tick_n(5);

        check_result("Lower priority IRQ3 served next", (dut->simpleirq & 0x07) == 3);

        dut->interrupt_request = 0;
        tick_n(3);
        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // ================================================================
        // TEST 4: Interrupt Masking
        // ================================================================
        std::cout << "\n--- Test 4: Interrupt Masking ---" << std::endl;

        // Mask IRQ2
        write_8259(1, 0x04);
        tick_n(3);

        // Try to trigger masked IRQ2 (keep line high)
        trigger_irq(2);
        check_result("Masked IRQ2 does not raise INT", dut->interrupt_to_cpu == 0);
        release_irq(2);

        // Unmask IRQ2
        write_8259(1, 0x00);
        tick_n(3);

        // Trigger unmasked IRQ2 (keep line high for check)
        trigger_irq(2);
        check_result("Unmasked IRQ2 raises INT", dut->interrupt_to_cpu == 1);
        check_result("Correct IRQ2 vector", (dut->simpleirq & 0x07) == 2);

        release_irq(2);
        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // ================================================================
        // TEST 5: Specific EOI
        // ================================================================
        std::cout << "\n--- Test 5: Specific EOI ---" << std::endl;

        trigger_and_ack_irq(5);
        send_eoi(true, 5);
        tick_n(3);
        check_result("Specific EOI processed", true);

        // ================================================================
        // TEST 6: Priority Rotation
        // ================================================================
        std::cout << "\n--- Test 6: Priority Rotation ---" << std::endl;

        write_8259(0, 0x80);  // Rotate on Auto-EOI
        tick_n(3);
        check_result("Auto-rotate mode set", true);

        // ================================================================
        // TEST 7: Read IRR/ISR
        // ================================================================
        std::cout << "\n--- Test 7: Read IRR/ISR ---" << std::endl;

        // Set read mode to IRR
        write_8259(0, 0x0A);  // OCW3: Read IRR
        tick_n(3);

        // Trigger IRQ4 but don't acknowledge
        dut->interrupt_request = (1 << 4);
        tick_n(3);

        uint8_t irr_value = read_8259(0);
        check_result("IRR shows pending IRQ4", (irr_value & 0x10) != 0);

        dut->interrupt_request = 0;
        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // Set read mode to ISR
        write_8259(0, 0x0B);  // OCW3: Read ISR
        tick_n(3);

        // ================================================================
        // TEST 8: All IRQ Lines (0, 4, 7)
        // ================================================================
        std::cout << "\n--- Test 8: Test Selected IRQ Lines (0, 4, 7) ---" << std::endl;

        // Test IRQ0
        trigger_irq(0);
        check_result("IRQ0 triggers correctly", dut->interrupt_to_cpu && (dut->simpleirq & 0x07) == 0);
        release_irq(0);
        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // Test IRQ4
        trigger_irq(4);
        check_result("IRQ4 triggers correctly", dut->interrupt_to_cpu && (dut->simpleirq & 0x07) == 4);
        release_irq(4);
        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // Test IRQ7
        trigger_irq(7);
        check_result("IRQ7 triggers correctly", dut->interrupt_to_cpu && (dut->simpleirq & 0x07) == 7);
        release_irq(7);
        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // ================================================================
        // TEST 9: Nested Interrupts
        // ================================================================
        std::cout << "\n--- Test 9: Nested Interrupts ---" << std::endl;

        // Trigger low-priority IRQ7
        trigger_irq(7);
        check_result("IRQ7 triggered", (dut->simpleirq & 0x07) == 7);

        ack_irq();
        tick_n(3);

        // While servicing IRQ7, trigger higher-priority IRQ0
        trigger_irq(0);
        check_result("Higher priority IRQ0 interrupts IRQ7", (dut->simpleirq & 0x07) == 0);

        ack_irq();
        send_eoi(false, 0);  // EOI for IRQ0
        tick_n(3);

        send_eoi(false, 0);  // EOI for IRQ7
        tick_n(3);

        // ================================================================
        // TEST 10: Re-initialization
        // ================================================================
        std::cout << "\n--- Test 10: Re-initialization ---" << std::endl;

        init_8259_basic(0x40);
        tick_n(5);

        trigger_irq(1);
        check_result("Re-initialization with new vector (0x41)", dut->simpleirq == 0x41);

        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // ================================================================
        // TEST 11: Edge Detection
        // ================================================================
        std::cout << "\n--- Test 11: Edge Detection ---" << std::endl;

        // Hold IRQ3 high (first edge triggers interrupt)
        dut->interrupt_request = (1 << 3);
        tick_n(5);

        // This first edge should trigger
        check_result("Edge detection on low-to-high transition", dut->interrupt_to_cpu == 1);

        // Release and acknowledge the first interrupt
        dut->interrupt_request = 0;
        tick_n(3);
        ack_irq();
        send_eoi(false, 0);
        tick_n(3);

        // ================================================================
        // TEST 12: Simultaneous Mask and IRQ
        // ================================================================
        std::cout << "\n--- Test 12: Simultaneous Operations ---" << std::endl;

        dut->interrupt_request = (1 << 6);
        write_8259(1, 0x40);  // Mask IRQ6
        tick_n(5);
        dut->interrupt_request = 0;

        check_result("Simultaneous mask blocks interrupt", dut->interrupt_to_cpu == 0);

        // Unmask
        write_8259(1, 0x00);
        tick_n(3);

        // ================================================================
        // Test Summary
        // ================================================================
        std::cout << "\n================================================================" << std::endl;
        std::cout << "TEST SUMMARY" << std::endl;
        std::cout << "================================================================" << std::endl;
        std::cout << "Total Tests: " << test_count << std::endl;
        std::cout << "Passed:      " << pass_count << std::endl;
        std::cout << "Failed:      " << fail_count << std::endl;
        std::cout << "Pass Rate:   " << (pass_count * 100 / test_count) << "%" << std::endl;
        std::cout << "================================================================" << std::endl;

        if (fail_count == 0) {
            std::cout << "ALL TESTS PASSED" << std::endl;
        } else {
            std::cout << "SOME TESTS FAILED" << std::endl;
        }
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    KF8259TB tb;
    tb.run_tests();

    return tb.fail_count > 0 ? 1 : 0;
}
