// ================================================================
// Verilator C++ Testbench for InsnDecoder
// Tests x86 instruction decoding state machine
// ================================================================

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "VInsnDecoder.h"
#include <iostream>
#include <iomanip>
#include <cstdlib>
#include <queue>

class InsnDecoder_TB {
private:
    VInsnDecoder* dut;
    VerilatedVcdC* tfp;
    uint64_t time_counter;
    int test_count;
    int pass_count;
    int fail_count;

    // Instruction byte queue
    std::queue<uint8_t> insn_queue;

    // Captured instruction fields
    uint8_t captured_opcode;
    uint8_t captured_mod_rm;
    uint16_t captured_displacement;
    bool captured_has_modrm;
    bool captured_has_segment_override;
    uint8_t captured_segment;
    uint8_t captured_rep;
    bool captured_lock;
    uint8_t captured_length;
    bool captured_invalid;

public:
    InsnDecoder_TB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VInsnDecoder;
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open("insndecoder_tb.vcd");

        // Initialize inputs
        dut->clk = 0;
        dut->reset = 1;
        dut->flush = 0;
        dut->stall = 0;
        dut->nearly_full = 0;
        dut->fifo_rd_data = 0;
        dut->fifo_empty = 1;
        dut->immed_complete = 0;
        dut->immediate = 0;

        // Initialize captured fields
        captured_opcode = 0;
        captured_mod_rm = 0;
        captured_displacement = 0;
        captured_has_modrm = false;
        captured_has_segment_override = false;
        captured_segment = 0;
        captured_rep = 0;
        captured_lock = false;
        captured_length = 0;
        captured_invalid = false;
    }

    ~InsnDecoder_TB() {
        tfp->close();
        delete tfp;
        delete dut;
    }

    // Single clock edge - evaluate and handle FIFO
    void tick() {
        // Update FIFO interface before clock edge
        if (!insn_queue.empty()) {
            dut->fifo_rd_data = insn_queue.front();
            dut->fifo_empty = 0;
        } else {
            dut->fifo_rd_data = 0;
            dut->fifo_empty = 1;
        }

        // Falling edge
        dut->clk = 0;
        dut->eval();
        tfp->dump(time_counter++);

        // Rising edge
        dut->clk = 1;
        dut->eval();
        tfp->dump(time_counter++);

        // Pop from queue if DUT read this cycle
        if (dut->fifo_rd_en && !insn_queue.empty()) {
            insn_queue.pop();
        }
    }

    void reset_dut() {
        dut->reset = 1;
        dut->flush = 0;
        dut->stall = 0;
        dut->immed_complete = 0;
        for (int i = 0; i < 3; i++) tick();
        dut->reset = 0;
        for (int i = 0; i < 2; i++) tick();
    }

    void clear_queue() {
        while (!insn_queue.empty()) insn_queue.pop();
    }

    void push_byte(uint8_t data) {
        insn_queue.push(data);
    }

    void capture_instruction() {
        captured_opcode = dut->instruction[0] & 0xFF;
        captured_mod_rm = (dut->instruction[0] >> 8) & 0xFF;
        captured_displacement = (dut->instruction[0] >> 16) & 0xFFFF;
        captured_has_modrm = (dut->instruction[2] >> 0) & 0x1;
        captured_has_segment_override = (dut->instruction[2] >> 1) & 0x1;
        captured_segment = (dut->instruction[2] >> 2) & 0x3;
        captured_rep = (dut->instruction[2] >> 4) & 0x3;
        captured_lock = (dut->instruction[2] >> 6) & 0x1;
        captured_length = (dut->instruction[2] >> 7) & 0xF;
        captured_invalid = (dut->instruction[2] >> 11) & 0x1;
    }

    // Wait for complete signal with proper handshaking
    bool wait_for_complete(int max_cycles = 100) {
        int timeout = 0;

        while (timeout < max_cycles) {
            // Check if complete is asserted
            if (dut->complete) {
                // Capture instruction immediately when complete is seen
                capture_instruction();
                return true;
            }

            // Handle immediate read requests from DUT
            if (dut->immed_start) {
                // Wait one cycle, then provide the immediate
                tick();

                // Set immediate value from queue
                if (!insn_queue.empty()) {
                    uint16_t imm_val = insn_queue.front();
                    if (!dut->immed_is_8bit && insn_queue.size() > 1) {
                        // For 16-bit, combine two bytes
                        std::queue<uint8_t> temp = insn_queue;
                        uint8_t lo = temp.front();
                        temp.pop();
                        if (!temp.empty()) {
                            imm_val = lo | (temp.front() << 8);
                        }
                    }
                    dut->immediate = imm_val;
                }

                // Assert immed_complete
                dut->immed_complete = 1;
                tick();
                dut->immed_complete = 0;
            } else {
                tick();
            }

            timeout++;
        }
        return false;
    }

    // Wait for instruction to be consumed (complete deasserted)
    void wait_instruction_consumed() {
        int timeout = 0;
        while (dut->complete && timeout < 20) {
            tick();
            timeout++;
        }
    }

    void check_pass(const char* test_name) {
        test_count++;
        std::cout << "[PASS] Test " << test_count << ": " << test_name << std::endl;
        pass_count++;
    }

    void check_fail(const char* test_name, const char* reason) {
        test_count++;
        std::cout << "[FAIL] Test " << test_count << ": " << test_name << std::endl;
        std::cout << "  Reason: " << reason << std::endl;
        fail_count++;
    }

    void run_tests() {
        std::cout << "========================================" << std::endl;
        std::cout << "InsnDecoder Testbench (Verilator)" << std::endl;
        std::cout << "========================================" << std::endl << std::endl;

        reset_dut();

        // ================================================================
        // TEST 1: Simple 1-byte instruction (NOP = 0x90)
        // ================================================================
        std::cout << "--- Test 1: Simple NOP instruction ---" << std::endl;
        clear_queue();
        push_byte(0x90);  // NOP

        if (wait_for_complete() && captured_opcode == 0x90 && !captured_has_modrm) {
            check_pass("Simple NOP instruction");
        } else {
            check_fail("Simple NOP instruction", "Decode failed");
            std::cout << "  opcode=0x" << std::hex << (int)captured_opcode
                      << " has_modrm=" << captured_has_modrm << std::dec << std::endl;
        }
        wait_instruction_consumed();

        // ================================================================
        // TEST 2: Instruction with segment override prefix
        // ================================================================
        std::cout << std::endl << "--- Test 2: Segment override prefix (ES:) ---" << std::endl;
        clear_queue();
        push_byte(0x26);  // ES: prefix
        push_byte(0x90);  // NOP

        if (wait_for_complete() && captured_opcode == 0x90 && captured_has_segment_override) {
            check_pass("Segment override prefix (ES:)");
        } else {
            check_fail("Segment override prefix (ES:)", "Prefix not detected");
            std::cout << "  opcode=0x" << std::hex << (int)captured_opcode
                      << " has_seg_override=" << captured_has_segment_override << std::dec << std::endl;
        }
        wait_instruction_consumed();

        // ================================================================
        // TEST 3: Instruction with ModR/M byte (MOV r/m8, r8 = 0x88)
        // ================================================================
        std::cout << std::endl << "--- Test 3: Instruction with ModR/M byte (MOV) ---" << std::endl;
        clear_queue();
        push_byte(0x88);  // MOV r/m8, r8 (has ModR/M per insn_has_modrm)
        push_byte(0xC0);  // ModR/M: mod=11, reg=0, rm=0 (AL, AL)

        if (wait_for_complete() && captured_opcode == 0x88 && captured_has_modrm && captured_mod_rm == 0xC0) {
            check_pass("Instruction with ModR/M byte (MOV)");
        } else {
            check_fail("Instruction with ModR/M byte (MOV)", "ModR/M decode failed");
            std::cout << "  opcode=0x" << std::hex << (int)captured_opcode
                      << " has_modrm=" << captured_has_modrm
                      << " mod_rm=0x" << (int)captured_mod_rm << std::dec << std::endl;
        }
        wait_instruction_consumed();

        // ================================================================
        // TEST 4: ADD r/m8, r8 (opcode 0x00) - verify ALU instructions work
        // ================================================================
        std::cout << std::endl << "--- Test 4: ADD r/m8, r8 (opcode 0x00) ---" << std::endl;
        clear_queue();
        push_byte(0x00);  // ADD r/m8, r8
        push_byte(0xC1);  // ModR/M: mod=11, reg=0, rm=1 (CL, AL)

        if (wait_for_complete() && captured_opcode == 0x00 && captured_has_modrm && captured_mod_rm == 0xC1) {
            check_pass("ADD r/m8, r8 (opcode 0x00)");
        } else {
            check_fail("ADD r/m8, r8 (opcode 0x00)", "ModR/M decode failed");
            std::cout << "  opcode=0x" << std::hex << (int)captured_opcode
                      << " has_modrm=" << captured_has_modrm
                      << " mod_rm=0x" << (int)captured_mod_rm << std::dec << std::endl;
        }
        wait_instruction_consumed();

        // ================================================================
        // TEST 5: REP prefix
        // ================================================================
        std::cout << std::endl << "--- Test 5: REP prefix ---" << std::endl;
        clear_queue();
        push_byte(0xF3);  // REP prefix
        push_byte(0xA4);  // MOVSB

        if (wait_for_complete() && captured_opcode == 0xA4 && captured_rep != 0) {
            check_pass("REP prefix");
        } else {
            check_fail("REP prefix", "REP not detected");
            std::cout << "  opcode=0x" << std::hex << (int)captured_opcode
                      << " rep=" << (int)captured_rep << std::dec << std::endl;
        }
        wait_instruction_consumed();

        // ================================================================
        // TEST 6: LOCK prefix
        // ================================================================
        std::cout << std::endl << "--- Test 6: LOCK prefix ---" << std::endl;
        clear_queue();
        push_byte(0xF0);  // LOCK prefix
        push_byte(0x90);  // NOP

        if (wait_for_complete() && captured_opcode == 0x90 && captured_lock) {
            check_pass("LOCK prefix");
        } else {
            check_fail("LOCK prefix", "LOCK not detected");
            std::cout << "  opcode=0x" << std::hex << (int)captured_opcode
                      << " lock=" << captured_lock << std::dec << std::endl;
        }
        wait_instruction_consumed();

        // ================================================================
        // TEST 7: Flush clears state
        // ================================================================
        std::cout << std::endl << "--- Test 7: Flush clears decoder state ---" << std::endl;
        clear_queue();
        push_byte(0x00);  // Start instruction
        tick();  // Let it start processing
        tick();
        dut->flush = 1;
        tick();
        dut->flush = 0;
        tick();

        if (!dut->complete) {
            check_pass("Flush clears decoder state");
        } else {
            check_fail("Flush clears decoder state", "Decoder not cleared");
        }

        // ================================================================
        // TEST 8: Reset clears state
        // ================================================================
        std::cout << std::endl << "--- Test 8: Reset clears decoder state ---" << std::endl;
        clear_queue();
        push_byte(0x90);
        wait_for_complete();
        dut->reset = 1;
        tick();
        dut->reset = 0;
        tick();

        if (!dut->complete) {
            check_pass("Reset clears decoder state");
        } else {
            check_fail("Reset clears decoder state", "Decoder not cleared");
        }

        // ================================================================
        // TEST 9: Multiple prefixes
        // ================================================================
        std::cout << std::endl << "--- Test 9: Multiple prefixes ---" << std::endl;
        clear_queue();
        push_byte(0x26);  // ES: prefix
        push_byte(0xF0);  // LOCK prefix
        push_byte(0x90);  // NOP

        if (wait_for_complete() && captured_has_segment_override && captured_lock) {
            check_pass("Multiple prefixes");
        } else {
            check_fail("Multiple prefixes", "Prefixes not detected");
            std::cout << "  has_seg_override=" << captured_has_segment_override
                      << " lock=" << captured_lock << std::endl;
        }

        // ================================================================
        // Summary
        // ================================================================
        std::cout << std::endl << "========================================" << std::endl;
        std::cout << "Test Summary" << std::endl;
        std::cout << "========================================" << std::endl;
        std::cout << "Total:  " << test_count << std::endl;
        std::cout << "Passed: " << pass_count << std::endl;
        std::cout << "Failed: " << fail_count << std::endl;

        if (fail_count == 0) {
            std::cout << std::endl << "ALL TESTS PASSED" << std::endl;
        } else {
            std::cout << std::endl << "SOME TESTS FAILED" << std::endl;
        }
        std::cout << "========================================" << std::endl;
    }

    int get_exit_code() {
        return (fail_count == 0) ? 0 : 1;
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    InsnDecoder_TB* tb = new InsnDecoder_TB();
    tb->run_tests();
    int exit_code = tb->get_exit_code();
    delete tb;

    return exit_code;
}
