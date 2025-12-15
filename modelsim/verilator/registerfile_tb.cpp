// ================================================================
// Verilator C++ Testbench for RegisterFile
// Tests x86 general purpose register file (AX, BX, CX, DX, SI, DI, BP, SP)
// ================================================================

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "VRegisterFile.h"
#include <iostream>
#include <iomanip>
#include <cstdlib>

// Register encoding (matching RegisterEnum.sv)
enum GPR16 { AX=0, CX=1, DX=2, BX=3, SP=4, BP=5, SI=6, DI=7 };
enum GPR8  { AL=0, CL=1, DL=2, BL=3, AH=4, CH=5, DH=6, BH=7 };

class RegisterFileTB {
private:
    VRegisterFile* dut;
    VerilatedVcdC* tfp;
    uint64_t time_counter;
    int test_count;
    int pass_count;
    int fail_count;

public:
    RegisterFileTB() : time_counter(0), test_count(0), pass_count(0), fail_count(0) {
        dut = new VRegisterFile;
        Verilated::traceEverOn(true);
        tfp = new VerilatedVcdC;
        dut->trace(tfp, 99);
        tfp->open("registerfile_tb.vcd");

        // Initialize inputs
        dut->clk = 0;
        dut->reset = 1;
        dut->is_8_bit = 0;
        dut->rd_sel[0] = 0;
        dut->rd_sel[1] = 0;
        dut->wr_sel = 0;
        dut->wr_val = 0;
        dut->wr_en = 0;
    }

    ~RegisterFileTB() {
        tfp->close();
        delete tfp;
        delete dut;
    }

    void tick() {
        dut->clk = 0;
        dut->eval();
        tfp->dump(time_counter++);

        dut->clk = 1;
        dut->eval();
        tfp->dump(time_counter++);
    }

    void reset_dut() {
        dut->reset = 1;
        for (int i = 0; i < 3; i++) tick();
        dut->reset = 0;
        tick();
    }

    void write_reg(uint8_t sel, uint16_t val) {
        dut->wr_sel = sel;
        dut->wr_val = val;
        dut->wr_en = 1;
        tick();
        dut->wr_en = 0;
        tick();
    }

    uint16_t read_reg(int port, uint8_t sel) {
        dut->rd_sel[port] = sel;
        tick();
        tick();  // Read latency
        return dut->rd_val[port];
    }

    void check_result(const char* test_name, uint16_t expected, uint16_t actual) {
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
        std::cout << "RegisterFile Testbench (Verilator)" << std::endl;
        std::cout << "========================================" << std::endl;

        reset_dut();

        //========================================
        // TEST 1: 16-bit Register Writes
        //========================================
        std::cout << std::endl << "--- TEST 1: 16-bit Register Writes ---" << std::endl;
        dut->is_8_bit = 0;

        // Write to AX (000)
        write_reg(AX, 0x1234);
        check_result("Write/Read AX", 0x1234, read_reg(0, AX));

        // Write to CX (001)
        write_reg(CX, 0x5678);
        check_result("Write/Read CX", 0x5678, read_reg(0, CX));

        // Write to DX (010)
        write_reg(DX, 0x9ABC);
        check_result("Write/Read DX", 0x9ABC, read_reg(0, DX));

        // Write to BX (011) - BX has direct output port
        write_reg(BX, 0xDEF0);
        tick();
        check_result("BX output port", 0xDEF0, dut->bx);

        //========================================
        // TEST 2: 8-bit Register Writes (Low Byte)
        //========================================
        std::cout << std::endl << "--- TEST 2: 8-bit Register Writes (Low Byte) ---" << std::endl;

        // First write a known 16-bit value to AX
        dut->is_8_bit = 0;
        write_reg(AX, 0x1200);

        // Now write to AL (low byte)
        dut->is_8_bit = 1;
        write_reg(AL, 0x00AA);

        // Read AX (16-bit mode)
        dut->is_8_bit = 0;
        check_result("Write AL, Read AX", 0x12AA, read_reg(0, AX));

        //========================================
        // TEST 3: 8-bit Register Writes (High Byte)
        //========================================
        std::cout << std::endl << "--- TEST 3: 8-bit Register Writes (High Byte) ---" << std::endl;

        // Write to AH (high byte)
        dut->is_8_bit = 1;
        write_reg(AH, 0x00BB);

        // Read AX (16-bit mode)
        dut->is_8_bit = 0;
        check_result("Write AH, Read AX", 0xBBAA, read_reg(0, AX));

        //========================================
        // TEST 4: Dual Read Ports
        //========================================
        std::cout << std::endl << "--- TEST 4: Dual Read Ports ---" << std::endl;
        dut->is_8_bit = 0;

        // Read AX and CX simultaneously
        dut->rd_sel[0] = AX;
        dut->rd_sel[1] = CX;
        tick();
        tick();
        check_result("Read Port 0 (AX)", 0xBBAA, dut->rd_val[0]);
        check_result("Read Port 1 (CX)", 0x5678, dut->rd_val[1]);

        //========================================
        // TEST 5: Write-Read Bypass
        //========================================
        std::cout << std::endl << "--- TEST 5: Write-Read Bypass ---" << std::endl;
        dut->is_8_bit = 0;

        // Set up read port and write same register simultaneously
        dut->rd_sel[0] = DX;
        dut->wr_sel = DX;
        dut->wr_val = 0xFFFF;
        dut->wr_en = 1;
        tick();
        tick();
        check_result("Bypass Logic", 0xFFFF, dut->rd_val[0]);
        dut->wr_en = 0;
        tick();

        //========================================
        // TEST 6: Special Register Outputs (SI, DI, BP, BX)
        //========================================
        std::cout << std::endl << "--- TEST 6: Special Register Outputs ---" << std::endl;
        dut->is_8_bit = 0;

        // Write to SI (110)
        write_reg(SI, 0xA5A5);
        tick();
        check_result("SI output port", 0xA5A5, dut->si);

        // Write to DI (111)
        write_reg(DI, 0x5A5A);
        tick();
        check_result("DI output port", 0x5A5A, dut->di);

        // Write to BP (101)
        write_reg(BP, 0x3C3C);
        tick();
        check_result("BP output port", 0x3C3C, dut->bp);

        //========================================
        // TEST 7: 8-bit BL/BH Register Operations
        //========================================
        std::cout << std::endl << "--- TEST 7: 8-bit BL/BH Register Operations ---" << std::endl;

        // First write a known value to BX
        dut->is_8_bit = 0;
        write_reg(BX, 0x0000);

        // Write to BL (011)
        dut->is_8_bit = 1;
        write_reg(BL, 0x00CC);
        tick();
        check_result("BX after BL write", 0x00CC, dut->bx);

        // Write to BH (111)
        write_reg(BH, 0x00DD);
        tick();
        check_result("BX after BH write", 0xDDCC, dut->bx);

        //========================================
        // Test Summary
        //========================================
        std::cout << std::endl << "========================================" << std::endl;
        std::cout << "RegisterFile Testbench Complete" << std::endl;
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

    RegisterFileTB* tb = new RegisterFileTB();
    tb->run_tests();
    int exit_code = tb->get_exit_code();
    delete tb;

    return exit_code;
}
