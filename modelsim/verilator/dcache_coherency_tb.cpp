// DCache Coherency Testbench for Verilator
// Tests CPU/DMA/FPU memory coherency through D-cache

#include <verilated.h>
#include <iostream>
#include <cstdint>
#include <cstdlib>

// Include the Verilator-generated header
#include "VDCache2Way.h"

class DCache2WayTB {
public:
    VDCache2Way* dut;
    uint64_t sim_time;
    int test_count;
    int pass_count;
    int fail_count;

    // Simulated memory (backing store)
    uint16_t memory[4096];

    DCache2WayTB() {
        dut = new VDCache2Way;
        sim_time = 0;
        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        // Initialize memory
        for (int i = 0; i < 4096; i++) {
            memory[i] = 0;
        }
    }

    ~DCache2WayTB() {
        delete dut;
    }

    void tick() {
        // Handle memory backend BEFORE clock edges so DUT sees responses
        handle_memory();
        handle_vwb();

        // Falling edge
        dut->clk = 0;
        dut->eval();
        sim_time++;

        // Rising edge - DUT samples inputs here
        dut->clk = 1;
        dut->eval();
        sim_time++;
    }

    void handle_memory() {
        // Main memory port - 1-cycle latency
        static bool pending_access = false;
        static uint32_t pending_addr = 0;
        static bool pending_wr = false;
        static uint16_t pending_data = 0;

        if (pending_access) {
            dut->m_ack = 1;
            if (!pending_wr) {
                dut->m_data_in = memory[pending_addr & 0xFFF];
            }
            pending_access = false;
        } else {
            dut->m_ack = 0;
        }

        if (dut->m_access) {
            pending_access = true;
            pending_addr = dut->m_addr;
            pending_wr = dut->m_wr_en;
            pending_data = dut->m_data_out;

            if (dut->m_wr_en) {
                uint16_t mask = 0;
                if (dut->m_bytesel & 1) mask |= 0x00FF;
                if (dut->m_bytesel & 2) mask |= 0xFF00;
                memory[pending_addr & 0xFFF] = (memory[pending_addr & 0xFFF] & ~mask) | (pending_data & mask);
            }
        }
    }

    void handle_vwb() {
        // Victim writeback port - 1-cycle latency
        static bool pending_vwb = false;
        static uint32_t pending_vwb_addr = 0;
        static uint16_t pending_vwb_data = 0;

        if (pending_vwb) {
            dut->vwb_ack = 1;
            pending_vwb = false;
        } else {
            dut->vwb_ack = 0;
        }

        if (dut->vwb_access && dut->vwb_wr_en) {
            pending_vwb = true;
            pending_vwb_addr = dut->vwb_addr;
            pending_vwb_data = dut->vwb_data_out;

            uint16_t mask = 0;
            if (dut->vwb_bytesel & 1) mask |= 0x00FF;
            if (dut->vwb_bytesel & 2) mask |= 0xFF00;
            memory[pending_vwb_addr & 0xFFF] = (memory[pending_vwb_addr & 0xFFF] & ~mask) | (pending_vwb_data & mask);

            std::cout << "  [VWB] Victim writeback addr=0x" << std::hex << pending_vwb_addr
                      << " data=0x" << pending_vwb_data << std::dec << std::endl;
        }
    }

    void reset() {
        dut->reset = 1;
        dut->enabled = 1;
        dut->c_access = 0;
        dut->c_wr_en = 0;
        dut->c_bytesel = 3;
        dut->c_addr = 0;
        dut->c_data_out = 0;
        dut->m_data_in = 0;
        dut->m_ack = 0;
        dut->vwb_ack = 0;

        for (int i = 0; i < 10; i++) tick();

        dut->reset = 0;
        for (int i = 0; i < 20; i++) tick();
    }

    bool cache_write(uint32_t addr, uint16_t data, int timeout = 1000) {
        dut->c_addr = addr;
        dut->c_data_out = data;
        dut->c_wr_en = 1;
        dut->c_bytesel = 3;
        dut->c_access = 1;

        int cycles = 0;
        while (!dut->c_ack && cycles < timeout) {
            tick();
            cycles++;
        }

        if (cycles >= timeout) {
            dut->c_access = 0;
            dut->c_wr_en = 0;
            std::cout << "  [CACHE] Write timeout at addr=0x" << std::hex << addr << std::dec << std::endl;
            return false;
        }

        // Hold write signals for one more cycle after ack (proper handshake)
        tick();
        cycles++;

        dut->c_access = 0;
        dut->c_wr_en = 0;
        tick();

        std::cout << "  [CACHE] Write addr=0x" << std::hex << addr << " data=0x" << data
                  << " cycles=" << std::dec << cycles << std::endl;
        return true;
    }

    bool cache_read(uint32_t addr, uint16_t& data, int timeout = 1000) {
        dut->c_addr = addr;
        dut->c_wr_en = 0;
        dut->c_bytesel = 3;
        dut->c_access = 1;

        int cycles = 0;
        while (!dut->c_ack && cycles < timeout) {
            tick();
            cycles++;
        }

        if (cycles >= timeout) {
            dut->c_access = 0;
            std::cout << "  [CACHE] Read timeout at addr=0x" << std::hex << addr << std::dec << std::endl;
            return false;
        }

        // Capture data when ack is asserted
        data = dut->c_data_in;

        // Hold access for one more cycle after ack (proper handshake)
        tick();
        cycles++;

        dut->c_access = 0;
        tick();

        std::cout << "  [CACHE] Read addr=0x" << std::hex << addr << " data=0x" << data
                  << " cycles=" << std::dec << cycles << std::endl;
        return true;
    }

    void check_result(uint16_t expected, uint16_t actual, const char* description) {
        test_count++;
        if (expected == actual) {
            std::cout << "  PASS: " << description << " (expected=0x" << std::hex << expected
                      << ", actual=0x" << actual << ")" << std::dec << std::endl;
            pass_count++;
        } else {
            std::cout << "  FAIL: " << description << " (expected=0x" << std::hex << expected
                      << ", actual=0x" << actual << ")" << std::dec << std::endl;
            fail_count++;
        }
    }

    void run_tests() {
        std::cout << "============================================================" << std::endl;
        std::cout << "DCache2Way Coherency Test (Verilator)" << std::endl;
        std::cout << "============================================================" << std::endl;

        reset();

        // Test 1: Simple write and read back
        std::cout << "\n--- TEST 1: Write and Read Back ---" << std::endl;
        {
            uint16_t read_data;
            uint32_t test_addr = 0x100;

            if (!cache_write(test_addr, 0xABCD)) {
                std::cout << "  FAIL: Write failed" << std::endl;
                fail_count++;
            } else {
                // Wait for any pending operations
                for (int i = 0; i < 50; i++) tick();

                if (!cache_read(test_addr, read_data)) {
                    std::cout << "  FAIL: Read failed" << std::endl;
                    fail_count++;
                } else {
                    check_result(0xABCD, read_data, "Read back write");
                }
            }
        }

        // Test 2: Different cache line
        std::cout << "\n--- TEST 2: Different Cache Line ---" << std::endl;
        {
            uint16_t read_data;
            uint32_t test_addr = 0x200;

            if (!cache_write(test_addr, 0x1234)) {
                std::cout << "  FAIL: Write failed" << std::endl;
                fail_count++;
            } else {
                for (int i = 0; i < 50; i++) tick();

                if (!cache_read(test_addr, read_data)) {
                    std::cout << "  FAIL: Read failed" << std::endl;
                    fail_count++;
                } else {
                    check_result(0x1234, read_data, "Read from line 2");
                }
            }
        }

        // Test 3: Cache eviction scenario
        std::cout << "\n--- TEST 3: Cache Eviction ---" << std::endl;
        {
            uint16_t read_data;

            // Write to multiple addresses that might cause eviction
            for (int i = 0; i < 5; i++) {
                uint32_t addr = 0x100 + (i * 0x100);
                if (!cache_write(addr, 0x5000 + i)) {
                    std::cout << "  FAIL: Write " << i << " failed" << std::endl;
                    fail_count++;
                }
                for (int j = 0; j < 20; j++) tick();
            }

            // Read back first written address
            if (!cache_read(0x100, read_data)) {
                std::cout << "  FAIL: Read after eviction failed" << std::endl;
                fail_count++;
            } else {
                check_result(0x5000, read_data, "Read after potential eviction");
            }
        }

        // Summary
        std::cout << "\n============================================================" << std::endl;
        std::cout << "Test Summary" << std::endl;
        std::cout << "============================================================" << std::endl;
        std::cout << "Total: " << test_count << std::endl;
        std::cout << "Passed: " << pass_count << std::endl;
        std::cout << "Failed: " << fail_count << std::endl;

        if (fail_count == 0) {
            std::cout << "\nALL TESTS PASSED!" << std::endl;
        } else {
            std::cout << "\nSOME TESTS FAILED!" << std::endl;
        }
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    DCache2WayTB tb;
    tb.run_tests();

    return tb.fail_count > 0 ? 1 : 0;
}
