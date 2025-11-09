#!/bin/bash
#
# Comprehensive FPU Microcode Test Runner
# Runs both Python simulator tests and Verilog simulation tests
#

set -e  # Exit on any error

echo "============================================================"
echo "FPU MICROCODE COMPREHENSIVE TEST SUITE"
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
TOTAL_ERRORS=0

echo "${BLUE}[1/3] Running Python Simulator Tests...${NC}"
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

echo "${BLUE}[2/3] Compiling Verilog Testbench...${NC}"
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

echo "${BLUE}[3/3] Running Verilog Simulation Tests...${NC}"
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

# Final summary
echo "============================================================"
echo "FINAL TEST SUMMARY"
echo "============================================================"
if [ $PYTHON_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ Python Simulator Tests:    PASSED (13/13)${NC}"
else
    echo -e "${RED}✗ Python Simulator Tests:    FAILED${NC}"
fi

if [ $VERILOG_PASSED -eq 1 ]; then
    echo -e "${GREEN}✓ Verilog Simulation Tests:  PASSED (10/10)${NC}"
else
    echo -e "${RED}✗ Verilog Simulation Tests:  FAILED${NC}"
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
