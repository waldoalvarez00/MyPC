#!/bin/bash
# Run VGA Complete Modes Test - All 15 video modes

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Create results directory
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_DIR="sim_results_vga_complete_$TIMESTAMP"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling VGA Complete Modes Test (All 15 Modes)"
echo "================================================================"
echo ""

echo "Compiling VGA modules and testbench..."
echo ""

iverilog -g2012 \
    -DICARUS \
    -o "$RESULTS_DIR/vga_complete_modes_tb" \
    -s vga_complete_modes_tb \
    -I../Quartus/rtl/VGA \
    -I../Quartus/rtl/CPU/cdc \
    vga_complete_modes_tb.sv \
    ../Quartus/rtl/VGA/VGARegisters.sv \
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
echo "Running VGA Complete Modes Test (All 15 Modes)"
echo "================================================================"
echo ""

# Run simulation
cd "$RESULTS_DIR"
./vga_complete_modes_tb 2>&1 | tee simulation.log
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
    echo -e "${RED}⚠ WARNING: Some tests failed. Check simulation.log for details.${NC}"

    # Show which tests failed
    echo ""
    echo "Failed tests:"
    grep "\[FAIL\]" "$RESULTS_DIR/simulation.log"
    exit 1
elif grep -q "*** ALL 15 VIDEO MODE TESTS PASSED ***" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${GREEN}✓✓✓ SUCCESS: All 15 video mode tests passed! ✓✓✓${NC}"
    echo ""
    echo "Complete coverage:"
    grep -A 8 "Verified modes:" "$RESULTS_DIR/simulation.log" | tail -7
    exit 0
else
    echo ""
    echo "⚠ WARNING: Could not determine test status"
    exit 1
fi
