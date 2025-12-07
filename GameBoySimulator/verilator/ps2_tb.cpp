// PS/2 Keyboard Testbench for Verilator
// Tests PS/2 keyboard model with simplified controller
//
// Build: make -f Makefile.ps2
// Run: ./obj_dir/Vps2_ctrl_sim

#include <iostream>
#include <cstdio>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vps2_ctrl_sim.h"
#include "../sim/ps2_keyboard_model_cpp.h"

// Global time for Verilator
vluint64_t main_time = 0;

double sc_time_stamp() {
    return main_time;
}

class PS2Testbench {
public:
    Vps2_ctrl_sim* dut;
    VerilatedVcdC* tfp;
    PS2KeyboardModelCpp* keyboard;

    // Test stats
    int tests_passed;
    int tests_failed;
    bool trace_enabled;
    bool debug_enabled;

    PS2Testbench(bool do_trace = false, bool debug = false)
        : trace_enabled(do_trace), debug_enabled(debug) {
        dut = new Vps2_ctrl_sim;
        keyboard = new PS2KeyboardModelCpp(debug);
        tests_passed = 0;
        tests_failed = 0;

        // Initialize trace
        if (trace_enabled) {
            Verilated::traceEverOn(true);
            tfp = new VerilatedVcdC;
            dut->trace(tfp, 99);
            tfp->open("ps2_test.vcd");
        } else {
            tfp = nullptr;
        }

        // Initialize DUT
        dut->clk = 0;
        dut->rst_n = 0;
        dut->io_address = 0;
        dut->io_read = 0;
        dut->io_write = 0;
        dut->io_writedata = 0;
        dut->kb_data_in = 0;
        dut->kb_data_valid = 0;
    }

    ~PS2Testbench() {
        if (tfp) {
            tfp->close();
            delete tfp;
        }
        delete dut;
        delete keyboard;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        dut->clk = 1;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        // Clear one-cycle signals
        dut->kb_data_valid = 0;
    }

    void reset() {
        dut->rst_n = 0;
        for (int i = 0; i < 10; i++) tick();
        dut->rst_n = 1;
        for (int i = 0; i < 5; i++) tick();

        // Reset keyboard model
        keyboard->reset();

        // Clear initial BAT response
        while (keyboard->hasData()) {
            uint8_t data;
            keyboard->getNextByte(data);
        }
    }

    // Send keyboard data to controller
    void sendKeyboardData(uint8_t data) {
        dut->kb_data_in = data;
        dut->kb_data_valid = 1;
        tick();
        dut->kb_data_valid = 0;

        // Allow data to propagate
        for (int i = 0; i < 3; i++) tick();
    }

    // Transfer all queued keyboard data to controller
    void transferKeyboardBuffer() {
        while (keyboard->hasData()) {
            uint8_t data;
            keyboard->getNextByte(data);
            sendKeyboardData(data);
        }
    }

    // Read from I/O port
    uint8_t ioRead(uint8_t port) {
        dut->io_address = port;
        dut->io_read = 1;
        tick();
        uint8_t data = dut->io_readdata;
        dut->io_read = 0;
        tick();
        return data;
    }

    // Write to I/O port
    void ioWrite(uint8_t port, uint8_t data) {
        dut->io_address = port;
        dut->io_writedata = data;
        dut->io_write = 1;
        tick();
        dut->io_write = 0;
        tick();
    }

    // Read data port (0x60)
    uint8_t readData() {
        return ioRead(0);
    }

    // Read status port (0x64)
    uint8_t readStatus() {
        return ioRead(4);
    }

    // Write data port (0x60)
    void writeData(uint8_t data) {
        ioWrite(0, data);
    }

    // Write command port (0x64)
    void writeCommand(uint8_t cmd) {
        ioWrite(4, cmd);
    }

    // Wait for output buffer full
    bool waitOutputBuffer(int timeout = 100) {
        for (int i = 0; i < timeout; i++) {
            if (readStatus() & 0x01) return true;
            tick();
        }
        return false;
    }

    // Test result helpers
    void testPass(const char* name) {
        printf("[PASS] %s\n", name);
        tests_passed++;
    }

    void testFail(const char* name, const char* reason) {
        printf("[FAIL] %s: %s\n", name, reason);
        tests_failed++;
    }

    // Run all tests
    void runAllTests() {
        printf("\n=== PS/2 Keyboard Model Tests ===\n\n");

        testReset();
        testSingleKeyPress();
        testKeyRelease();
        testExtendedKeys();
        testFunctionKeys();
        testEchoCommand();
        testReadID();
        testSetLEDs();
        testDisableEnable();
        testSetScanCodeSet();
        testControllerSelfTest();
        testControllerCommands();
        testStringTyping();
        testInterruptGeneration();
        testOutputBufferFull();

        printf("\n=== Test Summary ===\n");
        printf("Passed: %d\n", tests_passed);
        printf("Failed: %d\n", tests_failed);
        printf("Total:  %d\n", tests_passed + tests_failed);

        keyboard->printStats();
    }

    // Individual tests
    void testReset() {
        reset();

        // Send reset command
        keyboard->receiveCommand(0xFF);
        transferKeyboardBuffer();

        // Should get ACK and then BAT
        if (waitOutputBuffer()) {
            uint8_t ack = readData();
            if (ack == 0xFA) {
                testPass("Reset command ACK");
            } else {
                char buf[64];
                sprintf(buf, "Expected ACK 0xFA, got 0x%02X", ack);
                testFail("Reset command ACK", buf);
            }
        } else {
            testFail("Reset command ACK", "No response");
        }
    }

    void testSingleKeyPress() {
        reset();

        // Press 'A' key
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_A);
        transferKeyboardBuffer();

        if (waitOutputBuffer()) {
            uint8_t scancode = readData();
            // Set 2 scan code for 'A' is 0x1C
            if (scancode == 0x1C) {
                testPass("Single key press (A)");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0x1C, got 0x%02X", scancode);
                testFail("Single key press (A)", buf);
            }
        } else {
            testFail("Single key press (A)", "No data received");
        }
    }

    void testKeyRelease() {
        reset();

        // Press and release 'B' key
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_B);
        keyboard->keyRelease(PS2KeyboardModelCpp::KEY_B);
        transferKeyboardBuffer();

        // Read make code
        if (!waitOutputBuffer()) {
            testFail("Key release (B)", "No make code");
            return;
        }
        uint8_t make = readData();

        // Read break prefix (0xF0)
        if (!waitOutputBuffer()) {
            testFail("Key release (B)", "No break prefix");
            return;
        }
        uint8_t prefix = readData();

        // Read break code
        if (!waitOutputBuffer()) {
            testFail("Key release (B)", "No break code");
            return;
        }
        uint8_t brk = readData();

        // Set 2: make=0x32, break prefix=0xF0, break=0x32
        if (make == 0x32 && prefix == 0xF0 && brk == 0x32) {
            testPass("Key release (B)");
        } else {
            char buf[128];
            sprintf(buf, "Expected 0x32,0xF0,0x32 got 0x%02X,0x%02X,0x%02X",
                    make, prefix, brk);
            testFail("Key release (B)", buf);
        }
    }

    void testExtendedKeys() {
        reset();

        // Press Right Ctrl (extended key)
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_RCTRL);
        transferKeyboardBuffer();

        // Should get E0 prefix first
        if (!waitOutputBuffer()) {
            testFail("Extended key (RCtrl)", "No E0 prefix");
            return;
        }
        uint8_t prefix = readData();

        if (!waitOutputBuffer()) {
            testFail("Extended key (RCtrl)", "No scan code");
            return;
        }
        uint8_t scancode = readData();

        if (prefix == 0xE0) {
            testPass("Extended key (RCtrl)");
        } else {
            char buf[64];
            sprintf(buf, "Expected E0 prefix, got 0x%02X", prefix);
            testFail("Extended key (RCtrl)", buf);
        }
    }

    void testFunctionKeys() {
        reset();

        // Press F1
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_F1);
        transferKeyboardBuffer();

        if (waitOutputBuffer()) {
            uint8_t scancode = readData();
            // Set 2 scan code for F1 is 0x05
            if (scancode == 0x05) {
                testPass("Function key (F1)");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0x05, got 0x%02X", scancode);
                testFail("Function key (F1)", buf);
            }
        } else {
            testFail("Function key (F1)", "No data received");
        }
    }

    void testEchoCommand() {
        reset();

        // Send echo command
        keyboard->receiveCommand(0xEE);
        transferKeyboardBuffer();

        if (waitOutputBuffer()) {
            uint8_t response = readData();
            if (response == 0xEE) {
                testPass("Echo command");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0xEE, got 0x%02X", response);
                testFail("Echo command", buf);
            }
        } else {
            testFail("Echo command", "No response");
        }
    }

    void testReadID() {
        reset();

        // Send read ID command
        keyboard->receiveCommand(0xF2);
        transferKeyboardBuffer();

        // Read ACK
        if (!waitOutputBuffer()) {
            testFail("Read ID command", "No ACK");
            return;
        }
        uint8_t ack = readData();

        // Read ID byte 1
        if (!waitOutputBuffer()) {
            testFail("Read ID command", "No ID byte 1");
            return;
        }
        uint8_t id1 = readData();

        // Read ID byte 2
        if (!waitOutputBuffer()) {
            testFail("Read ID command", "No ID byte 2");
            return;
        }
        uint8_t id2 = readData();

        // MF2 keyboard ID: 0xAB 0x83
        if (ack == 0xFA && id1 == 0xAB && id2 == 0x83) {
            testPass("Read ID command");
        } else {
            char buf[128];
            sprintf(buf, "Expected FA,AB,83 got %02X,%02X,%02X", ack, id1, id2);
            testFail("Read ID command", buf);
        }
    }

    void testSetLEDs() {
        reset();

        // Send set LEDs command
        keyboard->receiveCommand(0xED);
        transferKeyboardBuffer();

        // Read ACK
        if (!waitOutputBuffer()) {
            testFail("Set LEDs command", "No ACK");
            return;
        }
        uint8_t ack = readData();

        if (ack != 0xFA) {
            testFail("Set LEDs command", "No ACK for command");
            return;
        }

        // Send LED parameter (Caps + Num = 0x06)
        keyboard->receiveCommand(0x06);
        transferKeyboardBuffer();

        // Read ACK for parameter
        if (!waitOutputBuffer()) {
            testFail("Set LEDs command", "No ACK for parameter");
            return;
        }
        ack = readData();

        // Check LED state
        if (ack == 0xFA &&
            keyboard->isCapsLock() &&
            keyboard->isNumLock() &&
            !keyboard->isScrollLock()) {
            testPass("Set LEDs command");
        } else {
            char buf[128];
            sprintf(buf, "LED state: Caps=%d Num=%d Scroll=%d",
                    keyboard->isCapsLock(), keyboard->isNumLock(),
                    keyboard->isScrollLock());
            testFail("Set LEDs command", buf);
        }
    }

    void testDisableEnable() {
        reset();

        // Disable keyboard
        keyboard->receiveCommand(0xF5);
        transferKeyboardBuffer();

        // Read ACK
        if (!waitOutputBuffer()) {
            testFail("Disable/Enable keyboard", "No ACK for disable");
            return;
        }
        readData();

        // Try to send key - should be ignored
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_A);

        if (keyboard->hasData()) {
            testFail("Disable/Enable keyboard", "Keyboard not disabled");
            return;
        }

        // Enable keyboard
        keyboard->receiveCommand(0xF4);
        transferKeyboardBuffer();

        if (!waitOutputBuffer()) {
            testFail("Disable/Enable keyboard", "No ACK for enable");
            return;
        }
        readData();

        // Now key should work
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_A);

        if (keyboard->hasData()) {
            testPass("Disable/Enable keyboard");
        } else {
            testFail("Disable/Enable keyboard", "Keyboard not re-enabled");
        }
    }

    void testSetScanCodeSet() {
        reset();

        // Send set scan code set command
        keyboard->receiveCommand(0xF0);
        transferKeyboardBuffer();

        // Read ACK
        if (!waitOutputBuffer()) {
            testFail("Set scan code set", "No ACK");
            return;
        }
        readData();

        // Query current set (parameter 0)
        keyboard->receiveCommand(0x00);
        transferKeyboardBuffer();

        // Read ACK
        if (!waitOutputBuffer()) {
            testFail("Set scan code set", "No ACK for query");
            return;
        }
        readData();

        // Read current set
        if (!waitOutputBuffer()) {
            testFail("Set scan code set", "No set response");
            return;
        }
        uint8_t current_set = readData();

        if (current_set == 2) {
            testPass("Set scan code set");
        } else {
            char buf[64];
            sprintf(buf, "Expected set 2, got %d", current_set);
            testFail("Set scan code set", buf);
        }
    }

    void testControllerSelfTest() {
        reset();

        // Send self-test command (0xAA)
        writeCommand(0xAA);

        // Wait for response
        for (int i = 0; i < 10; i++) tick();

        if (waitOutputBuffer()) {
            uint8_t result = readData();
            if (result == 0x55) {
                testPass("Controller self-test");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0x55, got 0x%02X", result);
                testFail("Controller self-test", buf);
            }
        } else {
            testFail("Controller self-test", "No response");
        }
    }

    void testControllerCommands() {
        reset();

        // Read config byte
        writeCommand(0x20);

        for (int i = 0; i < 10; i++) tick();

        if (!waitOutputBuffer()) {
            testFail("Controller read config", "No response");
            return;
        }
        uint8_t config = readData();

        // Write new config
        writeCommand(0x60);
        for (int i = 0; i < 5; i++) tick();
        writeData(config | 0x40);  // Set system flag

        for (int i = 0; i < 10; i++) tick();

        // Read back
        writeCommand(0x20);
        for (int i = 0; i < 10; i++) tick();

        if (waitOutputBuffer()) {
            uint8_t new_config = readData();
            if ((new_config & 0x40) != 0) {
                testPass("Controller read/write config");
            } else {
                char buf[64];
                sprintf(buf, "Config not updated: 0x%02X", new_config);
                testFail("Controller read/write config", buf);
            }
        } else {
            testFail("Controller read/write config", "No readback");
        }
    }

    void testStringTyping() {
        reset();

        // Type "hi"
        keyboard->typeString("hi");
        int buffer_size = keyboard->getBufferSize();

        // "hi" = h press/release + i press/release
        // Each: make + break prefix + break = 3 bytes per key = 6 total
        if (buffer_size >= 6) {
            testPass("String typing (buffer fill)");
        } else {
            char buf[64];
            sprintf(buf, "Expected >= 6 bytes, got %d", buffer_size);
            testFail("String typing (buffer fill)", buf);
        }

        // Transfer and read first scan code
        transferKeyboardBuffer();

        if (waitOutputBuffer()) {
            uint8_t first = readData();
            // 'H' scan code in Set 2 is 0x33
            if (first == 0x33) {
                testPass("String typing (H scan code)");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0x33 for H, got 0x%02X", first);
                testFail("String typing (H scan code)", buf);
            }
        } else {
            testFail("String typing (H scan code)", "No data");
        }
    }

    void testInterruptGeneration() {
        reset();

        // Ensure interrupts enabled in config
        writeCommand(0x20);
        for (int i = 0; i < 10; i++) tick();
        if (waitOutputBuffer()) readData();

        // IRQ should be low initially
        if (dut->irq_keyb != 0) {
            testFail("Interrupt generation", "IRQ not initially low");
            return;
        }

        // Send keyboard data
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_SPACE);
        transferKeyboardBuffer();

        // Check IRQ is raised
        for (int i = 0; i < 10; i++) tick();

        if (dut->irq_keyb == 1) {
            // Read data to clear IRQ
            readData();
            for (int i = 0; i < 5; i++) tick();

            if (dut->irq_keyb == 0) {
                testPass("Interrupt generation");
            } else {
                testFail("Interrupt generation", "IRQ not cleared on read");
            }
        } else {
            testFail("Interrupt generation", "IRQ not raised");
        }
    }

    void testOutputBufferFull() {
        reset();

        // Initially empty
        uint8_t status = readStatus();
        if (status & 0x01) {
            testFail("Output buffer full flag", "Initially not empty");
            return;
        }

        // Send keyboard data
        keyboard->keyPress(PS2KeyboardModelCpp::KEY_ENTER);
        transferKeyboardBuffer();

        // Should be full now
        for (int i = 0; i < 10; i++) tick();
        status = readStatus();

        if (status & 0x01) {
            // Read to clear
            readData();

            status = readStatus();
            if (!(status & 0x01)) {
                testPass("Output buffer full flag");
            } else {
                testFail("Output buffer full flag", "Not cleared after read");
            }
        } else {
            testFail("Output buffer full flag", "Not set after data");
        }
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    bool trace = false;
    bool debug = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--trace") == 0) trace = true;
        if (strcmp(argv[i], "--debug") == 0) debug = true;
    }

    PS2Testbench tb(trace, debug);
    tb.runAllTests();

    return (tb.tests_failed > 0) ? 1 : 0;
}
