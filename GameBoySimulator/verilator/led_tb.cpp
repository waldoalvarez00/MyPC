// MiSTer LED Testbench for Verilator
// Tests LED model with controller
//
// Build: make -f Makefile.led
// Run: ./obj_dir/Vled_ctrl_sim

#include <iostream>
#include <cstdio>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vled_ctrl_sim.h"
#include "../sim/led_model_cpp.h"

// Global time for Verilator
vluint64_t main_time = 0;

double sc_time_stamp() {
    return main_time;
}

class LEDTestbench {
public:
    Vled_ctrl_sim* dut;
    VerilatedVcdC* tfp;
    LEDModelCpp* led;

    // Test stats
    int tests_passed;
    int tests_failed;
    bool trace_enabled;
    bool debug_enabled;

    LEDTestbench(bool do_trace = false, bool debug = false)
        : trace_enabled(do_trace), debug_enabled(debug) {
        dut = new Vled_ctrl_sim;
        led = new LEDModelCpp(debug);
        tests_passed = 0;
        tests_failed = 0;

        // Initialize trace
        if (trace_enabled) {
            Verilated::traceEverOn(true);
            tfp = new VerilatedVcdC;
            dut->trace(tfp, 99);
            tfp->open("led_test.vcd");
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
        dut->disk_activity = 0;
    }

    ~LEDTestbench() {
        if (tfp) {
            tfp->close();
            delete tfp;
        }
        delete dut;
        delete led;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        dut->clk = 1;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        // Update LED model with DUT outputs
        led->setUserLED(dut->led_user);
        led->setPowerLED(dut->led_power);
        led->setDiskLED(dut->led_disk);
        led->setRegister(dut->led_register);
        led->update();
    }

    void reset() {
        dut->rst_n = 0;
        for (int i = 0; i < 10; i++) tick();
        dut->rst_n = 1;
        for (int i = 0; i < 5; i++) tick();

        // Reset LED model
        led->reset();
    }

    // I/O helpers
    uint8_t ioRead(uint8_t addr) {
        dut->io_address = addr;
        dut->io_read = 1;
        tick();
        uint8_t data = dut->io_readdata;
        dut->io_read = 0;
        tick();
        return data;
    }

    void ioWrite(uint8_t addr, uint8_t data) {
        dut->io_address = addr;
        dut->io_writedata = data;
        dut->io_write = 1;
        tick();
        dut->io_write = 0;
        tick();
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
        printf("\n=== MiSTer LED Model Tests ===\n\n");

        testRegisterReset();
        testRegisterWriteLow();
        testRegisterWriteHigh();
        testRegisterReadBack();
        testUserLED();
        testPowerLED();
        testDiskLED();
        testDiskActivity();
        testMultipleLEDs();
        testPatternBlink();
        testDutyCycle();
        testHistory();

        printf("\n=== Test Summary ===\n");
        printf("Passed: %d\n", tests_passed);
        printf("Failed: %d\n", tests_failed);
        printf("Total:  %d\n", tests_passed + tests_failed);

        led->printStats();
    }

    // Individual tests
    void testRegisterReset() {
        reset();

        if (dut->led_register == 0x0000) {
            testPass("Register reset to zero");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0x0000, got 0x%04X", dut->led_register);
            testFail("Register reset to zero", buf);
        }
    }

    void testRegisterWriteLow() {
        reset();

        // Write low byte
        ioWrite(0x00, 0xAA);

        if ((dut->led_register & 0xFF) == 0xAA) {
            testPass("Register write low byte");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0x00AA, got 0x%04X", dut->led_register);
            testFail("Register write low byte", buf);
        }
    }

    void testRegisterWriteHigh() {
        reset();

        // Write high byte
        ioWrite(0x01, 0x55);

        if ((dut->led_register >> 8) == 0x55) {
            testPass("Register write high byte");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0x5500, got 0x%04X", dut->led_register);
            testFail("Register write high byte", buf);
        }
    }

    void testRegisterReadBack() {
        reset();

        // Write both bytes
        ioWrite(0x00, 0x12);
        ioWrite(0x01, 0x34);

        // Read back
        uint8_t low = ioRead(0x00);
        uint8_t high = ioRead(0x01);

        if (low == 0x12 && high == 0x34) {
            testPass("Register read back");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0x12,0x34 got 0x%02X,0x%02X", low, high);
            testFail("Register read back", buf);
        }
    }

    void testUserLED() {
        reset();

        // Control register: bit 0 = USER LED
        ioWrite(0x02, 0x01);

        for (int i = 0; i < 5; i++) tick();

        if (dut->led_user == 1) {
            // Turn off
            ioWrite(0x02, 0x00);
            for (int i = 0; i < 5; i++) tick();

            if (dut->led_user == 0) {
                testPass("USER LED control");
            } else {
                testFail("USER LED control", "Failed to turn off");
            }
        } else {
            testFail("USER LED control", "Failed to turn on");
        }
    }

    void testPowerLED() {
        reset();

        // Control register: bit 1 = POWER mode, bit 2 = POWER on
        // Set user mode and turn on
        ioWrite(0x02, 0x06);  // 0000 0110 = mode + on

        for (int i = 0; i < 5; i++) tick();

        // Check mode and state
        if ((dut->led_power & 0x02) && (dut->led_power & 0x01)) {
            testPass("POWER LED control");
        } else {
            char buf[64];
            sprintf(buf, "Expected mode=1 state=1, got 0x%02X", dut->led_power);
            testFail("POWER LED control", buf);
        }
    }

    void testDiskLED() {
        reset();

        // Control register: bit 3 = DISK mode, bit 4 = DISK on
        // Set user mode and turn on
        ioWrite(0x02, 0x18);  // 0001 1000 = mode + on

        for (int i = 0; i < 5; i++) tick();

        // Check mode and state
        if ((dut->led_disk & 0x02) && (dut->led_disk & 0x01)) {
            testPass("DISK LED control");
        } else {
            char buf[64];
            sprintf(buf, "Expected mode=1 state=1, got 0x%02X", dut->led_disk);
            testFail("DISK LED control", buf);
        }
    }

    void testDiskActivity() {
        reset();

        // Keep DISK in system mode (mode=0)
        ioWrite(0x02, 0x00);

        // Check initial state
        if (dut->led_disk != 0) {
            testFail("Disk activity", "DISK LED not initially off");
            return;
        }

        // Trigger activity
        dut->disk_activity = 1;
        tick();
        dut->disk_activity = 0;

        // Check LED turned on
        for (int i = 0; i < 10; i++) tick();

        if ((dut->led_disk & 0x01) == 1) {
            // Wait for activity to expire (simplified - just check it turns off)
            for (int i = 0; i < 6000; i++) tick();

            if ((dut->led_disk & 0x01) == 0) {
                testPass("Disk activity");
            } else {
                testFail("Disk activity", "LED didn't turn off");
            }
        } else {
            testFail("Disk activity", "LED didn't turn on");
        }
    }

    void testMultipleLEDs() {
        reset();

        // Turn on all LEDs
        ioWrite(0x02, 0x1F);  // USER + POWER mode/on + DISK mode/on
        ioWrite(0x00, 0xFF);
        ioWrite(0x01, 0xFF);

        for (int i = 0; i < 10; i++) tick();

        bool all_on = dut->led_user &&
                      (dut->led_power == 0x03) &&
                      (dut->led_disk == 0x03) &&
                      (dut->led_register == 0xFFFF);

        if (all_on) {
            testPass("Multiple LEDs simultaneously");
        } else {
            char buf[128];
            sprintf(buf, "USER=%d POWER=0x%02X DISK=0x%02X REG=0x%04X",
                    dut->led_user, dut->led_power, dut->led_disk, dut->led_register);
            testFail("Multiple LEDs simultaneously", buf);
        }
    }

    void testPatternBlink() {
        reset();

        // Set blink pattern on LED model
        led->setPattern(LEDModelCpp::PATTERN_BLINK_FAST);

        // Run for a bit and check pattern changes
        bool saw_on = false;
        bool saw_off = false;

        for (int i = 0; i < 20000000; i++) {
            tick();
            if (led->getPatternState()) saw_on = true;
            else saw_off = true;

            if (saw_on && saw_off) break;
        }

        if (saw_on && saw_off) {
            testPass("Pattern blink");
        } else {
            char buf[64];
            sprintf(buf, "saw_on=%d saw_off=%d", saw_on, saw_off);
            testFail("Pattern blink", buf);
        }
    }

    void testDutyCycle() {
        reset();

        // Turn USER LED on
        ioWrite(0x02, 0x01);

        // Run for some cycles
        for (int i = 0; i < 1000; i++) tick();

        // Turn off for same duration
        ioWrite(0x02, 0x00);
        for (int i = 0; i < 1000; i++) tick();

        // Check duty cycle is around 50%
        float duty = led->getUserDutyCycle();

        // Allow some tolerance for reset cycles
        if (duty > 40.0f && duty < 60.0f) {
            testPass("Duty cycle tracking");
        } else {
            char buf[64];
            sprintf(buf, "Expected ~50%%, got %.1f%%", duty);
            testFail("Duty cycle tracking", buf);
        }
    }

    void testHistory() {
        reset();

        // Toggle USER LED several times
        for (int i = 0; i < 5; i++) {
            ioWrite(0x02, 0x01);
            for (int j = 0; j < 10; j++) tick();
            ioWrite(0x02, 0x00);
            for (int j = 0; j < 10; j++) tick();
        }

        // Check history has events
        const auto& history = led->getHistory();

        if (history.size() >= 10) {
            testPass("History tracking");
        } else {
            char buf[64];
            sprintf(buf, "Expected >= 10 events, got %zu", history.size());
            testFail("History tracking", buf);
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

    LEDTestbench tb(trace, debug);
    tb.runAllTests();

    return (tb.tests_failed > 0) ? 1 : 0;
}
