// ================================================================
// Verilator C++ Testbench for ImmediateReader
// Tests immediate value reading from instruction FIFO
// ================================================================

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "VImmediateReader.h"
#include <iostream>
#include <iomanip>
#include <queue>

class ImmediateReaderTB {
private:
    VImmediateReader* dut;
    VerilatedVcdC* tfp;
    uint64_t time_counter;
    int test_count;
    int pass_count;
    int fail_count;

    // Simulated FIFO
    std::queue<uint8_t> fifo_data;

public:
    ImmediateReaderTB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VImmediateReader;
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open("immediate_reader_tb.vcd");

        // Initialize inputs
        dut->clk = 0;
        dut->reset = 1;
        dut->start = 0;
        dut->flush = 0;
        dut->is_8bit = 0;
        dut->fifo_rd_data = 0;
        dut->fifo_empty = 1;
    }

    ~ImmediateReaderTB() {
        tfp->close();
        delete tfp;
        delete dut;
    }

    void update_fifo_outputs() {
        // Combinational read-through FIFO model
        if (!fifo_data.empty()) {
            dut->fifo_rd_data = fifo_data.front();
            dut->fifo_empty = 0;
        } else {
            dut->fifo_rd_data = 0;
            dut->fifo_empty = 1;
        }
    }

    // Evaluate combinational logic without clock edge
    void eval_comb() {
        update_fifo_outputs();
        dut->eval();
    }

    void tick() {
        // Update FIFO outputs first (combinational path)
        update_fifo_outputs();

        // Falling edge
        dut->clk = 0;
        dut->eval();
        tfp->dump(time_counter++);

        // Evaluate combinational logic to check fifo_rd_en
        bool do_read = dut->fifo_rd_en && !fifo_data.empty();

        // Rising edge
        dut->clk = 1;
        dut->eval();
        tfp->dump(time_counter++);

        // After rising edge: advance FIFO if read occurred
        if (do_read && !fifo_data.empty()) {
            fifo_data.pop();
            // Update outputs immediately for next combinational evaluation
            update_fifo_outputs();
            dut->eval();
        }
    }

    void reset_dut() {
        dut->reset = 1;
        // Clear FIFO
        while (!fifo_data.empty()) fifo_data.pop();
        update_fifo_outputs();
        for (int i = 0; i < 3; i++) tick();
        dut->reset = 0;
        tick();
    }

    void push_byte(uint8_t byte) {
        fifo_data.push(byte);
        update_fifo_outputs();
    }

    void clear_fifo() {
        while (!fifo_data.empty()) fifo_data.pop();
        update_fifo_outputs();
    }

    void check_result(const char* test_name, bool condition) {
        test_count++;
        if (condition) {
            std::cout << "[PASS] " << test_name << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] " << test_name << std::endl;
            std::cout << "       immediate=0x" << std::hex << std::setw(4)
                      << std::setfill('0') << dut->immediate
                      << ", busy=" << (int)dut->busy
                      << ", complete=" << (int)dut->complete << std::dec << std::endl;
            fail_count++;
        }
    }

    void check_result_value(const char* test_name, uint16_t expected, uint16_t actual) {
        test_count++;
        if (expected == actual) {
            std::cout << "[PASS] " << test_name << ": Expected 0x"
                      << std::hex << std::setw(4) << std::setfill('0') << expected
                      << ", Got 0x" << std::setw(4) << actual << std::dec << std::endl;
            pass_count++;
        } else {
            std::cout << "[FAIL] " << test_name << ": Expected 0x"
                      << std::hex << std::setw(4) << std::setfill('0') << expected
                      << ", Got 0x" << std::setw(4) << actual << std::dec << std::endl;
            fail_count++;
        }
    }

    void run_tests() {
        std::cout << "========================================" << std::endl;
        std::cout << "ImmediateReader Testbench (Verilator)" << std::endl;
        std::cout << "========================================" << std::endl;

        reset_dut();

        //========================================
        // TEST 1: 8-bit Immediate (Positive Value)
        //========================================
        std::cout << std::endl << "--- TEST 1: 8-bit Immediate (Positive) ---" << std::endl;

        clear_fifo();
        push_byte(0x42);  // Positive value

        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();  // Evaluate combinationally first

        // For 8-bit, complete should be asserted combinationally same cycle as start
        // immediate output is also combinational
        check_result("8-bit positive immediate (combinational)",
                     dut->immediate == 0x0042 && dut->complete);

        tick();  // Clock it through
        dut->start = 0;
        tick();
        tick();

        //========================================
        // TEST 2: 8-bit Immediate (Negative Value - Sign Extended)
        //========================================
        std::cout << std::endl << "--- TEST 2: 8-bit Immediate (Negative) ---" << std::endl;

        clear_fifo();
        push_byte(0xFF);  // -1 in signed 8-bit

        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();

        // Should be sign-extended to 0xFFFF
        check_result("8-bit negative immediate (sign extended)",
                     dut->immediate == 0xFFFF && dut->complete);

        tick();
        dut->start = 0;
        tick();
        tick();

        //========================================
        // TEST 3: 16-bit Immediate (Little Endian)
        //========================================
        std::cout << std::endl << "--- TEST 3: 16-bit Immediate ---" << std::endl;

        clear_fifo();
        push_byte(0x34);  // Low byte
        push_byte(0x12);  // High byte

        dut->is_8bit = 0;
        dut->start = 1;
        eval_comb();

        // For 16-bit, complete should NOT be asserted on first cycle
        check_result("16-bit immediate not complete on first cycle", !dut->complete);

        tick();  // Read first byte
        dut->start = 0;
        eval_comb();

        // After first byte read, complete should be asserted (bytes_read = 1)
        // Wait for complete
        for (int i = 0; i < 10 && !dut->complete; i++) tick();

        check_result("16-bit immediate (little endian)",
                     dut->immediate == 0x1234 && dut->complete);

        tick();
        tick();

        //========================================
        // TEST 4: Busy Signal
        //========================================
        std::cout << std::endl << "--- TEST 4: Busy Signal ---" << std::endl;

        clear_fifo();
        push_byte(0xAB);
        push_byte(0xCD);

        dut->is_8bit = 0;
        dut->start = 1;
        eval_comb();

        // Busy should be asserted (start & ~complete)
        check_result("Busy asserted during 16-bit fetch", dut->busy == 1);

        tick();
        dut->start = 0;
        for (int i = 0; i < 10 && !dut->complete; i++) tick();

        check_result("Busy deasserted after complete", dut->busy == 0 && dut->complete);
        check_result_value("16-bit value", 0xCDAB, dut->immediate);

        tick();
        tick();

        //========================================
        // TEST 5: Flush Operation
        //========================================
        std::cout << std::endl << "--- TEST 5: Flush Operation ---" << std::endl;

        // For flush test, only push one byte for a 16-bit read
        // This way we can test flush while waiting for second byte
        clear_fifo();
        push_byte(0x12);  // Only one byte

        dut->is_8bit = 0;
        dut->start = 1;
        tick();
        dut->start = 0;
        eval_comb();

        // Should be busy but not complete (waiting for second byte)
        check_result("Busy before flush (waiting for byte)", dut->busy == 1);
        check_result("Not complete before flush", dut->complete == 0);

        // Flush while waiting
        dut->flush = 1;
        tick();
        dut->flush = 0;
        eval_comb();

        check_result("Flush clears busy", dut->busy == 0);
        check_result("Flush clears complete", dut->complete == 0);

        tick();
        tick();

        //========================================
        // TEST 6: Sequential Reads
        //========================================
        std::cout << std::endl << "--- TEST 6: Sequential Reads ---" << std::endl;

        clear_fifo();
        push_byte(0x11);
        push_byte(0x22);
        push_byte(0x33);

        // First 8-bit read
        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();

        uint16_t first_val = dut->immediate;
        check_result("First read complete", dut->complete);

        tick();
        dut->start = 0;
        tick();

        // Second 8-bit read
        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();

        uint16_t second_val = dut->immediate;
        check_result("Second read complete", dut->complete);

        check_result_value("First sequential read", 0x0011, first_val);
        check_result_value("Second sequential read", 0x0022, second_val);

        tick();
        dut->start = 0;
        tick();
        tick();

        //========================================
        // TEST 7: Zero Value
        //========================================
        std::cout << std::endl << "--- TEST 7: Zero Value ---" << std::endl;

        clear_fifo();
        push_byte(0x00);

        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();

        check_result("Zero immediate value", dut->immediate == 0x0000 && dut->complete);

        tick();
        dut->start = 0;
        tick();
        tick();

        //========================================
        // TEST 8: Complete Signal Timing (8-bit combinational)
        //========================================
        std::cout << std::endl << "--- TEST 8: Complete Signal Timing ---" << std::endl;

        clear_fifo();
        push_byte(0x55);

        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();

        // For 8-bit, complete should be asserted combinationally with start
        check_result("8-bit complete is combinational with start", dut->complete == 1);

        tick();
        dut->start = 0;
        tick();
        tick();

        //========================================
        // TEST 9: Sign Extension Edge Cases
        //========================================
        std::cout << std::endl << "--- TEST 9: Sign Extension Edge Cases ---" << std::endl;

        clear_fifo();
        push_byte(0x80);  // -128 in signed 8-bit

        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();

        check_result("Sign extension of 0x80",
                     dut->immediate == 0xFF80 && dut->complete);

        tick();
        dut->start = 0;
        tick();

        //========================================
        // TEST 10: Boundary Value 0x7F (127)
        //========================================
        std::cout << std::endl << "--- TEST 10: Boundary Value 0x7F ---" << std::endl;

        clear_fifo();
        push_byte(0x7F);  // +127, no sign extension

        dut->is_8bit = 1;
        dut->start = 1;
        eval_comb();

        check_result("No sign extension of 0x7F",
                     dut->immediate == 0x007F && dut->complete);

        tick();
        dut->start = 0;
        tick();

        //========================================
        // TEST 11: 16-bit with all bits set
        //========================================
        std::cout << std::endl << "--- TEST 11: 16-bit 0xFFFF ---" << std::endl;

        clear_fifo();
        push_byte(0xFF);  // Low byte
        push_byte(0xFF);  // High byte

        dut->is_8bit = 0;
        dut->start = 1;
        tick();
        dut->start = 0;

        for (int i = 0; i < 10 && !dut->complete; i++) tick();

        check_result("16-bit 0xFFFF value",
                     dut->immediate == 0xFFFF && dut->complete);

        tick();
        tick();

        //========================================
        // TEST 12: FIFO empty during read (stall)
        //========================================
        std::cout << std::endl << "--- TEST 12: FIFO stall ---" << std::endl;

        clear_fifo();
        push_byte(0xAA);  // Only one byte for 16-bit read

        dut->is_8bit = 0;
        dut->start = 1;
        tick();
        dut->start = 0;
        eval_comb();

        // Should be busy but not complete (waiting for second byte)
        check_result("Busy while waiting for second byte", dut->busy == 1);
        check_result("Not complete with missing byte", dut->complete == 0);

        // Add second byte
        push_byte(0xBB);
        eval_comb();

        // Now should complete
        for (int i = 0; i < 5 && !dut->complete; i++) tick();

        check_result("Complete after second byte added",
                     dut->complete && dut->immediate == 0xBBAA);

        tick();
        tick();

        //========================================
        // Test Summary
        //========================================
        std::cout << std::endl << "========================================" << std::endl;
        std::cout << "ImmediateReader Testbench Complete" << std::endl;
        std::cout << "========================================" << std::endl;
        std::cout << "Total Tests: " << test_count << std::endl;
        std::cout << "Passed:      " << pass_count << std::endl;
        std::cout << "Failed:      " << fail_count << std::endl;
        if (fail_count == 0)
            std::cout << "STATUS: ALL TESTS PASSED!" << std::endl;
        else
            std::cout << "STATUS: SOME TESTS FAILED!" << std::endl;
        std::cout << "========================================" << std::endl;
    }

    int get_exit_code() {
        return (fail_count == 0) ? 0 : 1;
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    ImmediateReaderTB* tb = new ImmediateReaderTB();
    tb->run_tests();
    int exit_code = tb->get_exit_code();
    delete tb;

    return exit_code;
}
