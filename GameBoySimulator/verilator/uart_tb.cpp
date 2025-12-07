// UART Testbench for Verilator
// Tests UART model with simplified controller
//
// Build: make -f Makefile.uart
// Run: ./obj_dir/Vuart_ctrl_sim

#include <iostream>
#include <cstdio>
#include <cstring>
#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vuart_ctrl_sim.h"
#include "../sim/uart_model_cpp.h"

// Global time for Verilator
vluint64_t main_time = 0;

double sc_time_stamp() {
    return main_time;
}

class UARTTestbench {
public:
    Vuart_ctrl_sim* dut;
    VerilatedVcdC* tfp;
    UARTModelCpp* uart;

    // Test stats
    int tests_passed;
    int tests_failed;
    bool trace_enabled;
    bool debug_enabled;

    UARTTestbench(bool do_trace = false, bool debug = false)
        : trace_enabled(do_trace), debug_enabled(debug) {
        dut = new Vuart_ctrl_sim;
        uart = new UARTModelCpp(debug);
        tests_passed = 0;
        tests_failed = 0;

        // Initialize trace
        if (trace_enabled) {
            Verilated::traceEverOn(true);
            tfp = new VerilatedVcdC;
            dut->trace(tfp, 99);
            tfp->open("uart_test.vcd");
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
        dut->rx_data_in = 0;
        dut->rx_data_valid = 0;
        dut->cts_in = 1;
        dut->dsr_in = 1;
        dut->dcd_in = 0;
        dut->ri_in = 0;
    }

    ~UARTTestbench() {
        if (tfp) {
            tfp->close();
            delete tfp;
        }
        delete dut;
        delete uart;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        dut->clk = 1;
        dut->eval();
        if (tfp) tfp->dump(main_time++);

        // Transfer TX data to model
        if (dut->tx_data_valid) {
            uart->receive(dut->tx_data_out);
        }

        // Clear one-cycle signals
        dut->rx_data_valid = 0;
    }

    void reset() {
        dut->rst_n = 0;
        for (int i = 0; i < 10; i++) tick();
        dut->rst_n = 1;
        for (int i = 0; i < 5; i++) tick();

        // Reset UART model
        uart->reset();
    }

    // I/O helpers
    uint8_t ioRead(uint8_t addr) {
        dut->io_address = addr;
        dut->io_read = 1;
        tick();  // Address latched, data available next cycle
        tick();  // Data now available (registered output)
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

    // Send data to DUT RX
    void sendToRX(uint8_t data) {
        dut->rx_data_in = data;
        dut->rx_data_valid = 1;
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
        printf("\n=== UART Model Tests ===\n\n");

        testReset();
        testScratchRegister();
        testDivisorLatch();
        testLineControl();
        testTransmit();
        testReceive();
        testLoopback();
        testFIFO();
        testModemControl();
        testModemStatus();
        testInterrupt();
        testStringTransmit();

        printf("\n=== Test Summary ===\n");
        printf("Passed: %d\n", tests_passed);
        printf("Failed: %d\n", tests_failed);
        printf("Total:  %d\n", tests_passed + tests_failed);

        uart->printStats();
    }

    // Individual tests
    void testReset() {
        reset();

        // Check LSR has THRE and TEMT set
        uint8_t lsr = ioRead(5);

        if ((lsr & 0x60) == 0x60) {
            testPass("Reset state");
        } else {
            char buf[64];
            sprintf(buf, "Expected LSR 0x60, got 0x%02X", lsr);
            testFail("Reset state", buf);
        }
    }

    void testScratchRegister() {
        reset();

        // Write and read scratch register
        ioWrite(7, 0xA5);
        uint8_t scr = ioRead(7);

        if (scr == 0xA5) {
            testPass("Scratch register");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0xA5, got 0x%02X", scr);
            testFail("Scratch register", buf);
        }
    }

    void testDivisorLatch() {
        reset();

        // Set DLAB
        ioWrite(3, 0x80);

        // Write divisor
        ioWrite(0, 0x0C);  // Low byte
        ioWrite(1, 0x00);  // High byte

        // Read back
        uint8_t dll = ioRead(0);
        uint8_t dlm = ioRead(1);

        // Clear DLAB
        ioWrite(3, 0x00);

        if (dll == 0x0C && dlm == 0x00) {
            testPass("Divisor latch");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0x0C,0x00 got 0x%02X,0x%02X", dll, dlm);
            testFail("Divisor latch", buf);
        }
    }

    void testLineControl() {
        reset();

        // Set 8N1
        ioWrite(3, 0x03);
        uint8_t lcr = ioRead(3);

        if (lcr == 0x03) {
            testPass("Line control (8N1)");
        } else {
            char buf[64];
            sprintf(buf, "Expected 0x03, got 0x%02X", lcr);
            testFail("Line control (8N1)", buf);
        }
    }

    void testTransmit() {
        reset();

        // Write to THR
        ioWrite(0, 0x41);  // 'A'

        // Wait for transmission
        for (int i = 0; i < 10; i++) tick();

        // Check model received it
        if (uart->getBytesRX() >= 1) {
            testPass("Transmit single byte");
        } else {
            testFail("Transmit single byte", "Data not received by model");
        }
    }

    void testReceive() {
        reset();

        // Send data to DUT
        sendToRX(0x42);  // 'B'

        // Check LSR shows data ready
        uint8_t lsr = ioRead(5);

        if (lsr & 0x01) {
            // Read data
            uint8_t data = ioRead(0);

            if (data == 0x42) {
                testPass("Receive single byte");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0x42, got 0x%02X", data);
                testFail("Receive single byte", buf);
            }
        } else {
            testFail("Receive single byte", "No data ready");
        }
    }

    void testLoopback() {
        reset();

        // Enable loopback
        ioWrite(4, 0x10);

        // Write to THR
        ioWrite(0, 0x55);

        // Should appear in RX
        for (int i = 0; i < 5; i++) tick();

        uint8_t lsr = ioRead(5);
        if (lsr & 0x01) {
            uint8_t data = ioRead(0);
            if (data == 0x55) {
                testPass("Loopback mode");
            } else {
                char buf[64];
                sprintf(buf, "Expected 0x55, got 0x%02X", data);
                testFail("Loopback mode", buf);
            }
        } else {
            testFail("Loopback mode", "No data in RX");
        }
    }

    void testFIFO() {
        reset();

        // Enable FIFO
        ioWrite(2, 0x01);

        // Send multiple bytes with spacing for FIFO to update
        for (int i = 0; i < 5; i++) {
            sendToRX(0x30 + i);  // '0', '1', '2', '3', '4'
            tick();  // Extra cycle for FIFO state to settle
        }

        // Read back
        bool all_ok = true;
        for (int i = 0; i < 5; i++) {
            uint8_t data = ioRead(0);
            if (data != (0x30 + i)) {
                all_ok = false;
                break;
            }
        }

        if (all_ok) {
            testPass("FIFO operations");
        } else {
            testFail("FIFO operations", "Data mismatch");
        }
    }

    void testModemControl() {
        reset();

        // Set DTR and RTS
        ioWrite(4, 0x03);

        // Check outputs
        for (int i = 0; i < 5; i++) tick();

        if (dut->dtr_out && dut->rts_out) {
            testPass("Modem control outputs");
        } else {
            char buf[64];
            sprintf(buf, "DTR=%d RTS=%d", dut->dtr_out, dut->rts_out);
            testFail("Modem control outputs", buf);
        }
    }

    void testModemStatus() {
        reset();

        // Set modem inputs
        dut->cts_in = 1;
        dut->dsr_in = 1;
        dut->dcd_in = 1;
        dut->ri_in = 0;

        for (int i = 0; i < 5; i++) tick();

        uint8_t msr = ioRead(6);

        // Check status bits (CTS, DSR, DCD should be set)
        if ((msr & 0xB0) == 0xB0) {
            testPass("Modem status inputs");
        } else {
            char buf[64];
            sprintf(buf, "Expected MSR 0xB0, got 0x%02X", msr);
            testFail("Modem status inputs", buf);
        }
    }

    void testInterrupt() {
        reset();

        // Enable RX data available interrupt
        ioWrite(1, 0x01);

        // Enable OUT2 (interrupt gate)
        ioWrite(4, 0x08);

        // IRQ should be low
        if (dut->irq != 0) {
            testFail("Interrupt generation", "IRQ high before data");
            return;
        }

        // Send data
        sendToRX(0x00);

        for (int i = 0; i < 5; i++) tick();

        // IRQ should be high
        if (dut->irq == 1) {
            // Read data to clear
            ioRead(0);
            for (int i = 0; i < 5; i++) tick();

            if (dut->irq == 0) {
                testPass("Interrupt generation");
            } else {
                testFail("Interrupt generation", "IRQ not cleared");
            }
        } else {
            testFail("Interrupt generation", "IRQ not raised");
        }
    }

    void testStringTransmit() {
        reset();

        const char* str = "Hello";
        int len = strlen(str);

        // Transmit string
        for (int i = 0; i < len; i++) {
            ioWrite(0, str[i]);
            for (int j = 0; j < 5; j++) tick();
        }

        // Wait for all transmissions
        for (int i = 0; i < 50; i++) tick();

        // Check model received all bytes
        if (uart->getBytesRX() >= (uint32_t)len) {
            testPass("String transmit");
        } else {
            char buf[64];
            sprintf(buf, "Expected %d bytes, got %u", len, uart->getBytesRX());
            testFail("String transmit", buf);
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

    UARTTestbench tb(trace, debug);
    tb.runAllTests();

    return (tb.tests_failed > 0) ? 1 : 0;
}
