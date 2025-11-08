#!/bin/bash
# Run VGA Mode Definitions testbench

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

# Create results directory
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_DIR="sim_results_vga_modes_$TIMESTAMP"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling VGA Mode Definitions Testbench"
echo "================================================================"
echo ""

echo "Compiling mode definitions and testbench..."
echo ""

iverilog -g2012 \
    -o "$RESULTS_DIR/vga_modes_tb" \
    -s vga_modes_tb \
    vga_modes_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo -e "${RED}Compilation failed!${NC}"
    echo "Check $RESULTS_DIR/compile.log for details"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running VGA Mode Definitions Test"
echo "================================================================"
echo ""

# Run simulation
cd "$RESULTS_DIR"
./vga_modes_tb 2>&1 | tee simulation.log
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
elif grep -q "*** ALL MODE DEFINITION TESTS PASSED ***" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${GREEN}✓✓✓ SUCCESS: All mode definition tests passed! ✓✓✓${NC}"
    exit 0
else
    echo ""
    echo "⚠ WARNING: Could not determine test status"
    exit 1
fi
