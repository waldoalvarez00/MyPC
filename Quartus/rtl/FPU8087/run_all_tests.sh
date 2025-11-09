#!/bin/bash
#
# Comprehensive FPU Microcode Test Runner
# Runs both Python simulator tests and Verilog simulation tests
#

set -e  # Exit on any error

echo "============================================================"
echo "FPU COMPREHENSIVE TEST SUITE"
echo "============================================================"
echo ""

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Track test results
PYTHON_PASSED=0
VERILOG_PASSED=0
INTERFACE_PASSED=0
INTEGRATION_PASSED=0
CPU_FPU_PASSED=0
TOTAL_ERRORS=0

echo "${BLUE}[1/6] Running Python Simulator Tests...${NC}"
echo "------------------------------------------------------------"
if python3 test_microcode.py > python_test_output.txt 2>&1; then
    cat python_test_output.txt
    PYTHON_PASSED=1
    echo -e "${GREEN}✓ Python tests PASSED${NC}"
else
    cat python_test_output.txt
    echo -e "${RED}✗ Python tests FAILED${NC}"
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
fi
echo ""

echo "${BLUE}[2/6] Running FPU-CPU Interface Tests...${NC}"
echo "------------------------------------------------------------"
if python3 test_fpu_interface.py > interface_test_output.txt 2>&1; then
    cat interface_test_output.txt
    INTERFACE_PASSED=1
    echo -e "${GREEN}✓ Interface tests PASSED${NC}"
else
    cat interface_test_output.txt
    echo -e "${RED}✗ Interface tests FAILED${NC}"
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
fi
echo ""

echo "${BLUE}[3/6] Compiling Verilog Testbench...${NC}"
echo "------------------------------------------------------------"
if iverilog -o tb_microcode tb_microcode.v absunit.sv \
    8087Status.v AddSubComp.v BarrelShifter.v BitShifter.v ByteShifter.v \
    CORDIC_Rotator.v ControlWord.v LZCByte.v LZCbit.v MathConstants.v \
    RoundUnit.v StackRegister.v myxorgate.v sequencer.v tagRegister.v \
    three_bit_4x1_mux.v 2>&1 | tee verilog_compile.log; then
    echo -e "${GREEN}✓ Verilog compilation PASSED${NC}"
else
    echo -e "${RED}✗ Verilog compilation FAILED${NC}"
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
fi
echo ""

echo "${BLUE}[4/6] Running Verilog Simulation Tests...${NC}"
echo "------------------------------------------------------------"
if vvp tb_microcode > verilog_test_output.txt 2>&1; then
    cat verilog_test_output.txt
    # Check if all tests passed
    if grep -q "ALL TESTS PASSED" verilog_test_output.txt; then
        VERILOG_PASSED=1
        echo -e "${GREEN}✓ Verilog tests PASSED${NC}"
    else
        echo -e "${RED}✗ Verilog tests FAILED${NC}"
        TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    fi
else
    cat verilog_test_output.txt
    echo -e "${RED}✗ Verilog simulation FAILED${NC}"
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
fi
echo ""

echo "${BLUE}[5/6] Running FPU Integration Tests...${NC}"
echo "------------------------------------------------------------"
# Compile integration testbench
if iverilog -o tb_fpu_integration_simple tb_fpu_integration_simple.v \
    FPU8087_Integrated.v FPU_Instruction_Decoder.v FPU_CPU_Interface.v FPU_Core_Wrapper.v 2>&1 | tee integration_compile.log; then
    echo -e "${GREEN}✓ Integration testbench compiled${NC}"

    # Run integration tests
    if vvp tb_fpu_integration_simple > integration_test_output.txt 2>&1; then
        cat integration_test_output.txt
        if grep -q "ALL TESTS PASSED" integration_test_output.txt; then
            INTEGRATION_PASSED=1
            echo -e "${GREEN}✓ Integration tests PASSED${NC}"
        else
            echo -e "${RED}✗ Integration tests FAILED${NC}"
            TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
        fi
    else
        cat integration_test_output.txt
        echo -e "${RED}✗ Integration simulation FAILED${NC}"
        TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    fi
else
    echo -e "${RED}✗ Integration testbench compilation FAILED${NC}"
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
fi
echo ""

echo "${BLUE}[6/6] Running CPU-FPU Connection Tests...${NC}"
echo "------------------------------------------------------------"
# Compile CPU-FPU connection testbench
if iverilog -o tb_cpu_fpu_final tb_cpu_fpu_final.v \
    CPU_FPU_Adapter.v FPU8087_Integrated.v FPU_Instruction_Decoder.v FPU_CPU_Interface.v FPU_Core_Wrapper.v 2>&1 | tee cpu_fpu_compile.log; then
    echo -e "${GREEN}✓ CPU-FPU testbench compiled${NC}"

    # Run CPU-FPU connection tests
    if vvp tb_cpu_fpu_final > cpu_fpu_test_output.txt 2>&1; then
        cat cpu_fpu_test_output.txt
        if grep -q "ALL TESTS PASSED" cpu_fpu_test_output.txt; then
            CPU_FPU_PASSED=1
            echo -e "${GREEN}✓ CPU-FPU connection tests PASSED${NC}"
        else
            echo -e "${RED}✗ CPU-FPU connection tests FAILED${NC}"
            TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
        fi
    else
        cat cpu_fpu_test_output.txt
        echo -e "${RED}✗ CPU-FPU simulation FAILED${NC}"
        TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
    fi
else
    echo -e "${RED}✗ CPU-FPU testbench compilation FAILED${NC}"
    TOTAL_ERRORS=$((TOTAL_ERRORS + 1))
fi
echo ""

# Final summary
echo "============================================================"
echo "FINAL TEST SUMMARY"
echo "============================================================"
if [ $PYTHON_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ Python Simulator Tests:    PASSED (13/13)${NC}"
else
    echo -e "${RED}✗ Python Simulator Tests:    FAILED${NC}"
fi

if [ $INTERFACE_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ FPU-CPU Interface Tests:   PASSED (12/12)${NC}"
else
    echo -e "${RED}✗ FPU-CPU Interface Tests:   FAILED${NC}"
fi

if [ $VERILOG_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ Verilog Simulation Tests:  PASSED (10/10)${NC}"
else
    echo -e "${RED}✗ Verilog Simulation Tests:  FAILED${NC}"
fi

if [ $INTEGRATION_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ FPU Integration Tests:     PASSED (5/5)${NC}"
else
    echo -e "${RED}✗ FPU Integration Tests:     FAILED${NC}"
fi

if [ $CPU_FPU_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ CPU-FPU Connection Tests:  PASSED (5/5)${NC}"
else
    echo -e "${RED}✗ CPU-FPU Connection Tests:  FAILED${NC}"
fi
echo "------------------------------------------------------------"

if [ $TOTAL_ERRORS -eq 0 ]; then
    echo -e "${GREEN}"
    echo "🎉 ALL TEST SUITES PASSED! 🎉"
    echo -e "${NC}"
    exit 0
else
    echo -e "${RED}"
    echo "❌ SOME TEST SUITES FAILED (Errors: $TOTAL_ERRORS)"
    echo -e "${NC}"
    exit 1
fi
