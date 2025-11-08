#!/bin/bash
#================================================================
# UART 16750 Test Script
# Compiles and runs comprehensive UART testbench for Icarus Verilog
#================================================================

# Color codes for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "================================================================"
echo "UART 16750 Controller Test"
echo "================================================================"

# Change to script directory
cd "$(dirname "$0")"

# Create results directory with timestamp
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_DIR="sim_results_uart_${TIMESTAMP}"
mkdir -p "$RESULTS_DIR"

echo ""
echo "Compiling UART modules..."

# Compile UART 16750 (VHDL files need to be compiled to Verilog or use mixed simulation)
# For Icarus Verilog, we need Verilog files only
# The uart.v wrapper instantiates uart_16750 which is VHDL

# Check if we can use GHDL + Icarus or just skip VHDL for now
# For now, let's try compiling just the Verilog wrapper and see what happens

iverilog -g2012 -DICARUS \
    -I../Quartus/rtl/uart16750 \
    -o uart_test \
    ../Quartus/rtl/uart16750/uart.v \
    uart_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

COMPILE_STATUS=$?

if [ $COMPILE_STATUS -ne 0 ]; then
    echo -e "${RED}✗✗✗ COMPILATION FAILED ✗✗✗${NC}"
    echo "Check $RESULTS_DIR/compile.log for details"
    echo ""
    echo "Note: UART 16750 uses VHDL implementation which requires GHDL."
    echo "Attempting to provide guidance..."
    echo ""
    echo "The UART 16750 is implemented in VHDL. You have two options:"
    echo "1. Use GHDL to compile VHDL files and link with Icarus Verilog"
    echo "2. Use a VHDL simulator like GHDL or ModelSim"
    echo ""
    echo "For GHDL + Icarus approach:"
    echo "  ghdl -a ../Quartus/rtl/uart16750/*.vhd"
    echo "  ghdl -e uart_16750"
    echo ""
    exit 1
fi

echo ""
echo "Running simulation..."
echo ""

# Run simulation
timeout 10 ./uart_test 2>&1 | tee "$RESULTS_DIR/simulation.log"

SIM_STATUS=$?

echo ""
echo "================================================================"
echo "Simulation Complete"
echo "================================================================"
echo ""
echo "Results saved to: $RESULTS_DIR"
echo ""
echo "Generated files:"
echo "  - compile.log    : Compilation messages"
echo "  - simulation.log : Simulation output and test results"
if [ -f "uart_tb.vcd" ]; then
    mv uart_tb.vcd "$RESULTS_DIR/"
    echo "  - uart_tb.vcd    : Waveform data (moved to results dir)"
fi

# Extract test summary
echo ""
echo "Test Results Summary:"
echo "---------------------"
grep -A 5 "Test Summary" "$RESULTS_DIR/simulation.log" || echo "No test summary found"

# Check for success
if grep -q "ALL TESTS PASSED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${GREEN}✓✓✓ SUCCESS: All UART tests passed! ✓✓✓${NC}"
    exit 0
elif grep -q "SOME TESTS FAILED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${YELLOW}⚠ WARNING: Some tests failed ⚠${NC}"
    exit 1
else
    echo ""
    echo -e "${RED}✗✗✗ ERROR: Simulation did not complete properly ✗✗✗${NC}"
    exit 1
fi
