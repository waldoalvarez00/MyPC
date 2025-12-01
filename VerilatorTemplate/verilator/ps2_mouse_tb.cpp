// PS/2 Mouse Testbench for Verilator
// Tests PS/2 mouse model with simplified controller
//
// Build: make -f Makefile.ps2mouse
// Run: ./obj_dir/Vps2_mouse_ctrl_sim

#include <iostream>
#include <cstdio>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vps2_mouse_ctrl_sim.h"
#include "../sim/ps2_mouse_model_cpp.h"

// Global time for Verilator
vluint64_t main_time = 0;

double sc_time_stamp() {
    return main_time;
}

class PS2MouseTestbench {
public:
    Vps2_mouse_ctrl_sim* dut;
    VerilatedVcdC* tfp;
    PS2MouseModelCpp* mouse;

    // Test stats
    int tests_passed;
    int tests_failed;
    bool trace_enabled;
    bool debug_enabled;

    PS2MouseTestbench(bool do_trace = false, bool debug = false)
        : trace_enabled(do_trace), debug_enabled(debug) {
        dut = new Vps2_mouse_ctrl_sim;
        mouse = new PS2MouseModelCpp(debug);
        tests_passed = 0;
        tests_failed = 0;

        // Initialize trace
        if (trace_enabled) {
            Verilated::traceEverOn(true);
            tfp = new VerilatedVcdC;
            dut->trace(tfp, 99);
            tfp->open("ps2_mouse_test.vcd");
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
        dut->mouse_data_in = 0;
        dut->mouse_data_valid = 0;
    }

    ~PS2MouseTestbench() {
        if (tfp) {
            tfp->close();
            delete tfp;
        }
        delete dut;
        delete mouse;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        dut->clk = 1;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        // Check for command to mouse
        if (dut->mouse_cmd_valid) {
            mouse->receiveCommand(dut->mouse_cmd_out);
        }

        // Clear one-cycle signals
        dut->mouse_data_valid = 0;
    }

    void reset() {
        dut->rst_n = 0;
        for (int i = 0; i < 10; i++) tick();
        dut->rst_n = 1;
        for (int i = 0; i < 5; i++) tick();

        // Reset mouse model
        mouse->reset();

        // Clear initial BAT response and device ID
        while (mouse->hasData()) {
            uint8_t data;
            mouse->getNextByte(data);
        }
    }

    // Send mouse data to controller
    void sendMouseData(uint8_t data) {
        dut->mouse_data_in = data;
        dut->mouse_data_valid = 1;
        tick();
        dut->mouse_data_valid = 0;

        // Allow data to propagate
        for (int i = 0; i < 3; i++) tick();
    }

    // Transfer all queued mouse data to controller
    void transferMouseBuffer() {
        while (mouse->hasData()) {
            uint8_t data;
            mouse->getNextByte(data);
            sendMouseData(data);
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

    // Send command to mouse via controller
    void sendMouseCommand(uint8_t cmd) {
        writeCommand(0xD4);  // Write to mouse
        for (int i = 0; i < 3; i++) tick();
        writeData(cmd);
        for (int i = 0; i < 5; i++) tick();
        // Command is automatically forwarded to mouse in tick()
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
        printf("\n=== PS/2 Mouse Model Tests ===\n\n");

        testReset();
        testDeviceID();
        testEnableDisable();
        testMovementPacket();
        testButtonStates();
        testNegativeMovement();
        testOverflow();
        testIntellimouseDetection();
        testScrollWheel();
        testSetSampleRate();
        testSetResolution();
        testStatusRequest();
        testRemoteMode();
        testControllerSelfTest();
        testMouseTest();
        testInterruptGeneration();

        printf("\n=== Test Summary ===\n");
        printf("Passed: %d\n", tests_passed);
        printf("Failed: %d\n", tests_failed);
        printf("Total:  %d\n", tests_passed + tests_failed);

        mouse->printStats();
    }

    // Individual tests
    void testReset() {
        reset();

        // Send reset command
        sendMouseCommand(0xFF);
        transferMouseBuffer();

        // Should get ACK, BAT, and device ID
        if (!waitOutputBuffer()) {
            testFail("Reset command", "No response");
            return;
        }
        uint8_t ack = readData();

        if (!waitOutputBuffer()) {
            testFail("Reset command", "No BAT");
            return;
        }
        uint8_t bat = readData();

        if (!waitOutputBuffer()) {
            testFail("Reset command", "No device ID");
            return;
        }
        uint8_t id = readData();

        if (ack == 0xFA && bat == 0xAA && id == 0x00) {
            testPass("Reset command");
        } else {
            char buf[128];
            sprintf(buf, "Expected FA,AA,00 got %02X,%02X,%02X", ack, bat, id);
            testFail("Reset command", buf);
        }
    }

    void testDeviceID() {
        reset();

        // Send get device ID command
        sendMouseCommand(0xF2);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Get device ID", "No ACK");
            return;
        }
        uint8_t ack = readData();

        if (!waitOutputBuffer()) {
            testFail("Get device ID", "No ID");
            return;
        }
        uint8_t id = readData();

        if (ack == 0xFA && id == 0x00) {
            testPass("Get device ID");
        } else {
            char buf[64];
            sprintf(buf, "Expected FA,00 got %02X,%02X", ack, id);
            testFail("Get device ID", buf);
        }
    }

    void testEnableDisable() {
        reset();

        // Disable reporting
        sendMouseCommand(0xF5);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Enable/Disable reporting", "No ACK for disable");
            return;
        }
        readData();

        // Try to send packet - should not work
        mouse->setButton(PS2MouseModelCpp::BTN_LEFT, true);
        mouse->move(10, 10);
        mouse->sendPacket();

        if (mouse->hasData()) {
            testFail("Enable/Disable reporting", "Packet sent while disabled");
            return;
        }

        // Enable reporting
        sendMouseCommand(0xF4);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Enable/Disable reporting", "No ACK for enable");
            return;
        }
        readData();

        // Now packet should work
        mouse->sendPacket();

        if (mouse->hasData()) {
            testPass("Enable/Disable reporting");
        } else {
            testFail("Enable/Disable reporting", "No packet after enable");
        }
    }

    void testMovementPacket() {
        reset();

        // Enable reporting
        sendMouseCommand(0xF4);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        // Move mouse
        mouse->move(50, 30);
        mouse->sendPacket();
        transferMouseBuffer();

        // Read packet
        if (!waitOutputBuffer()) {
            testFail("Movement packet", "No byte 1");
            return;
        }
        uint8_t byte1 = readData();

        if (!waitOutputBuffer()) {
            testFail("Movement packet", "No X movement");
            return;
        }
        uint8_t dx = readData();

        if (!waitOutputBuffer()) {
            testFail("Movement packet", "No Y movement");
            return;
        }
        uint8_t dy = readData();

        // Check values
        // byte1 should have bit 3 set, no buttons, no overflow, positive
        if ((byte1 & 0x08) && dx == 50 && dy == 30) {
            testPass("Movement packet");
        } else {
            char buf[128];
            sprintf(buf, "byte1=0x%02X dx=%d dy=%d", byte1, dx, dy);
            testFail("Movement packet", buf);
        }
    }

    void testButtonStates() {
        reset();

        // Enable reporting
        sendMouseCommand(0xF4);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        // Set buttons
        mouse->setButton(PS2MouseModelCpp::BTN_LEFT, true);
        mouse->setButton(PS2MouseModelCpp::BTN_RIGHT, true);
        mouse->sendPacket();
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Button states", "No packet");
            return;
        }
        uint8_t byte1 = readData();

        // Clear rest of packet
        if (waitOutputBuffer()) readData();
        if (waitOutputBuffer()) readData();

        // Check buttons: L=bit0, R=bit1, M=bit2
        if ((byte1 & 0x03) == 0x03) {
            testPass("Button states");
        } else {
            char buf[64];
            sprintf(buf, "Expected L+R buttons, got 0x%02X", byte1);
            testFail("Button states", buf);
        }
    }

    void testNegativeMovement() {
        reset();

        // Enable reporting
        sendMouseCommand(0xF4);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        // Move negative
        mouse->move(-40, -20);
        mouse->sendPacket();
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Negative movement", "No byte 1");
            return;
        }
        uint8_t byte1 = readData();

        if (!waitOutputBuffer()) {
            testFail("Negative movement", "No X");
            return;
        }
        int8_t dx = (int8_t)readData();

        if (!waitOutputBuffer()) {
            testFail("Negative movement", "No Y");
            return;
        }
        int8_t dy = (int8_t)readData();

        // Check sign bits (bit 4 = X sign, bit 5 = Y sign)
        bool x_neg = (byte1 & 0x10) != 0;
        bool y_neg = (byte1 & 0x20) != 0;

        if (x_neg && y_neg && dx == -40 && dy == -20) {
            testPass("Negative movement");
        } else {
            char buf[128];
            sprintf(buf, "byte1=0x%02X dx=%d dy=%d", byte1, dx, dy);
            testFail("Negative movement", buf);
        }
    }

    void testOverflow() {
        reset();

        // Enable reporting
        sendMouseCommand(0xF4);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        // Move beyond limits
        mouse->move(300, -300);
        mouse->sendPacket();
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Overflow handling", "No packet");
            return;
        }
        uint8_t byte1 = readData();

        // Clear rest
        if (waitOutputBuffer()) readData();
        if (waitOutputBuffer()) readData();

        // Check overflow bits (bit 6 = X overflow, bit 7 = Y overflow)
        bool x_ovf = (byte1 & 0x40) != 0;
        bool y_ovf = (byte1 & 0x80) != 0;

        if (x_ovf && y_ovf) {
            testPass("Overflow handling");
        } else {
            char buf[64];
            sprintf(buf, "Expected overflow bits, got 0x%02X", byte1);
            testFail("Overflow handling", buf);
        }
    }

    void testIntellimouseDetection() {
        reset();

        // Intellimouse detection sequence: set sample rate 200, 100, 80
        sendMouseCommand(0xF3);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        mouse->receiveCommand(200);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        sendMouseCommand(0xF3);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        mouse->receiveCommand(100);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        sendMouseCommand(0xF3);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        mouse->receiveCommand(80);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        // Check device ID - should be 0x03 for wheel mouse
        sendMouseCommand(0xF2);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Intellimouse detection", "No ACK");
            return;
        }
        readData();

        if (!waitOutputBuffer()) {
            testFail("Intellimouse detection", "No ID");
            return;
        }
        uint8_t id = readData();

        if (id == 0x03) {
            testPass("Intellimouse detection");
        } else {
            char buf[64];
            sprintf(buf, "Expected ID 0x03, got 0x%02X", id);
            testFail("Intellimouse detection", buf);
        }
    }

    void testScrollWheel() {
        reset();

        // Force wheel mouse mode
        mouse->setMouseType(PS2MouseModelCpp::MOUSE_WHEEL);

        // Enable reporting
        sendMouseCommand(0xF4);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        // Scroll
        mouse->scroll(3);
        mouse->sendPacket();
        transferMouseBuffer();

        // Read 4-byte packet
        if (!waitOutputBuffer()) {
            testFail("Scroll wheel", "No byte 1");
            return;
        }
        readData();  // byte 1

        if (!waitOutputBuffer()) {
            testFail("Scroll wheel", "No X");
            return;
        }
        readData();  // X

        if (!waitOutputBuffer()) {
            testFail("Scroll wheel", "No Y");
            return;
        }
        readData();  // Y

        if (!waitOutputBuffer()) {
            testFail("Scroll wheel", "No scroll byte");
            return;
        }
        int8_t scroll = (int8_t)(readData() & 0x0F);
        if (scroll > 7) scroll -= 16;  // Sign extend 4-bit value

        if (scroll == 3) {
            testPass("Scroll wheel");
        } else {
            char buf[64];
            sprintf(buf, "Expected scroll=3, got %d", scroll);
            testFail("Scroll wheel", buf);
        }
    }

    void testSetSampleRate() {
        reset();

        // Set sample rate
        sendMouseCommand(0xF3);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Set sample rate", "No ACK");
            return;
        }
        readData();

        // Send rate value
        mouse->receiveCommand(200);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Set sample rate", "No ACK for value");
            return;
        }
        readData();

        if (mouse->getSampleRate() == 200) {
            testPass("Set sample rate");
        } else {
            char buf[64];
            sprintf(buf, "Expected 200, got %d", mouse->getSampleRate());
            testFail("Set sample rate", buf);
        }
    }

    void testSetResolution() {
        reset();

        // Set resolution
        sendMouseCommand(0xE8);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Set resolution", "No ACK");
            return;
        }
        readData();

        // Send resolution value (0-3)
        mouse->receiveCommand(3);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Set resolution", "No ACK for value");
            return;
        }
        readData();

        if (mouse->getResolution() == 3) {
            testPass("Set resolution");
        } else {
            char buf[64];
            sprintf(buf, "Expected 3, got %d", mouse->getResolution());
            testFail("Set resolution", buf);
        }
    }

    void testStatusRequest() {
        reset();

        // Enable and set some state
        sendMouseCommand(0xF4);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        mouse->setButton(PS2MouseModelCpp::BTN_LEFT, true);

        // Request status
        sendMouseCommand(0xE9);
        transferMouseBuffer();

        if (!waitOutputBuffer()) {
            testFail("Status request", "No ACK");
            return;
        }
        readData();

        // Read 3-byte status
        if (!waitOutputBuffer()) {
            testFail("Status request", "No status byte 1");
            return;
        }
        uint8_t status1 = readData();

        if (!waitOutputBuffer()) {
            testFail("Status request", "No resolution");
            return;
        }
        uint8_t res = readData();

        if (!waitOutputBuffer()) {
            testFail("Status request", "No sample rate");
            return;
        }
        uint8_t rate = readData();

        // Check enabled bit and left button
        if ((status1 & 0x20) && (status1 & 0x04) && rate == 100) {
            testPass("Status request");
        } else {
            char buf[128];
            sprintf(buf, "status=0x%02X res=%d rate=%d", status1, res, rate);
            testFail("Status request", buf);
        }
    }

    void testRemoteMode() {
        reset();

        // Set remote mode
        sendMouseCommand(0xF0);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        if (!mouse->isStreamMode()) {
            // Set some state
            mouse->move(25, 15);
            mouse->setButton(PS2MouseModelCpp::BTN_MIDDLE, true);

            // Read data command
            sendMouseCommand(0xEB);
            transferMouseBuffer();

            if (!waitOutputBuffer()) {
                testFail("Remote mode", "No ACK");
                return;
            }
            readData();

            // Should get packet
            if (waitOutputBuffer()) {
                testPass("Remote mode");
                // Drain packet
                readData();
                if (waitOutputBuffer()) readData();
                if (waitOutputBuffer()) readData();
            } else {
                testFail("Remote mode", "No packet after read data");
            }
        } else {
            testFail("Remote mode", "Still in stream mode");
        }
    }

    void testControllerSelfTest() {
        reset();

        // Controller self-test
        writeCommand(0xAA);

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

    void testMouseTest() {
        reset();

        // Mouse interface test
        writeCommand(0xA9);

        for (int i = 0; i < 10; i++) tick();

        if (waitOutputBuffer()) {
            uint8_t result = readData();
            if (result == 0x00) {
                testPass("Mouse interface test");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0x00, got 0x%02X", result);
                testFail("Mouse interface test", buf);
            }
        } else {
            testFail("Mouse interface test", "No response");
        }
    }

    void testInterruptGeneration() {
        reset();

        // Enable reporting
        sendMouseCommand(0xF4);
        transferMouseBuffer();
        if (waitOutputBuffer()) readData();

        // IRQ should be low initially
        if (dut->irq_mouse != 0) {
            testFail("Interrupt generation", "IRQ not initially low");
            return;
        }

        // Send mouse packet
        mouse->move(10, 10);
        mouse->sendPacket();
        transferMouseBuffer();

        // Check IRQ is raised
        for (int i = 0; i < 10; i++) tick();

        if (dut->irq_mouse == 1) {
            // Read data to clear IRQ
            readData();
            for (int i = 0; i < 5; i++) tick();

            // IRQ should clear when buffer empty
            // Drain remaining bytes
            while (waitOutputBuffer(10)) {
                readData();
            }

            for (int i = 0; i < 5; i++) tick();

            if (dut->irq_mouse == 0) {
                testPass("Interrupt generation");
            } else {
                testFail("Interrupt generation", "IRQ not cleared");
            }
        } else {
            testFail("Interrupt generation", "IRQ not raised");
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

    PS2MouseTestbench tb(trace, debug);
    tb.runAllTests();

    return (tb.tests_failed > 0) ? 1 : 0;
}
