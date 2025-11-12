#!/bin/bash
#================================================================
# Simple UART Test Script
# Compiles and runs simple UART testbench for Icarus Verilog
#================================================================

# Color codes for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "================================================================"
echo "Simple UART Controller Test"
echo "================================================================"

# Change to script directory
cd "$(dirname "$0")"

# Create results directory with timestamp
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_DIR="sim_results_simple_uart_${TIMESTAMP}"
mkdir -p "$RESULTS_DIR"

echo ""
echo "Compiling Simple UART modules..."

# Compile Simple UART (SystemVerilog)
iverilog -g2012 -DICARUS \
    -I../Quartus/rtl/uart \
    -o simple_uart_test \
    ../Quartus/rtl/uart/BaudRateGen.sv \
    ../Quartus/rtl/uart/Receiver.sv \
    ../Quartus/rtl/uart/Transmitter.sv \
    ../Quartus/rtl/uart/Uart.sv \
    simple_uart_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

COMPILE_STATUS=$?

if [ $COMPILE_STATUS -ne 0 ]; then
    echo -e "${RED}✗✗✗ COMPILATION FAILED ✗✗✗${NC}"
    echo "Check $RESULTS_DIR/compile.log for details"
    exit 1
fi

echo ""
echo "Running simulation..."
echo ""

# Run simulation
timeout 30 vvp simple_uart_test 2>&1 | tee "$RESULTS_DIR/simulation.log"

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
if [ -f "simple_uart.vcd" ]; then
    mv simple_uart.vcd "$RESULTS_DIR/"
    echo "  - simple_uart.vcd : Waveform data (moved to results dir)"
fi

# Extract test summary
echo ""
echo "Test Results Summary:"
echo "---------------------"
grep -A 5 "Test Summary" "$RESULTS_DIR/simulation.log" || echo "No test summary found"

# Check for success
if grep -q "ALL TESTS PASSED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${GREEN}✓✓✓ SUCCESS: All simple UART tests passed! ✓✓✓${NC}"
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
