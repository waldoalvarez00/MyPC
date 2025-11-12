#!/bin/bash
# Run VGA Mode Switching Integration Test

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

# Create results directory
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_DIR="sim_results_vga_mode_switching_$TIMESTAMP"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling VGA Mode Switching Integration Test"
echo "================================================================"
echo ""

echo "Compiling VGA modules and testbench..."
echo ""

iverilog -g2012 \
    -DICARUS \
    -o "$RESULTS_DIR/vga_mode_switching_tb" \
    -s vga_mode_switching_tb \
    -I../Quartus/rtl/VGA \
    -I../Quartus/rtl/CPU/cdc \
    vga_mode_switching_tb.sv \
    ../Quartus/rtl/VGA/VGARegisters.sv \
    ../Quartus/rtl/VGA/VGASync.sv \
    ../Quartus/rtl/CPU/cdc/BusSync.sv \
    ../Quartus/rtl/CPU/cdc/MCP.sv \
    ../Quartus/rtl/CPU/cdc/SyncPulse.sv \
    ../Quartus/rtl/CPU/cdc/BitSync.sv \
    DACRam_sim.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo -e "${RED}Compilation failed!${NC}"
    echo "Check $RESULTS_DIR/compile.log for details"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running VGA Mode Switching Integration Test"
echo "================================================================"
echo ""

# Run simulation
cd "$RESULTS_DIR"
vvp vga_mode_switching_tb 2>&1 | tee simulation.log
SIM_RESULT=${PIPESTATUS[0]}
cd ..

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
echo ""

# Extract and display test summary
echo "Test Results Summary:"
echo "---------------------"
grep -A 5 "Test Summary" "$RESULTS_DIR/simulation.log" | tail -6

# Check for failures
if grep -q "*** SOME TESTS FAILED ***" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${RED}⚠ WARNING: Some tests may have failed. Check simulation.log for details.${NC}"
    exit 1
elif grep -q "*** ALL MODE SWITCHING TESTS PASSED ***" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${GREEN}✓✓✓ SUCCESS: All mode switching tests passed! ✓✓✓${NC}"
    exit 0
else
    echo ""
    echo "⚠ WARNING: Could not determine test status"
    exit 1
fi
