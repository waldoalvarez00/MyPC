#!/bin/bash
# Run CGA Controller Integration Test

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Create results directory
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_DIR="sim_results_cga_integration_$TIMESTAMP"
mkdir -p "$RESULTS_DIR"

# Copy hex files
cp cga.hex "$RESULTS_DIR/" 2>/dev/null || echo "Warning: cga.hex not found"
cp splash.hex "$RESULTS_DIR/" 2>/dev/null || echo "Warning: splash.hex not found"

echo "================================================================"
echo "Compiling CGA Controller Integration Test"
echo "================================================================"
echo ""

echo "Compiling all CGA modules and testbench..."
echo ""

iverilog -g2012 \
    -DICARUS \
    -o "$RESULTS_DIR/cga_controller_integration_tb" \
    -s cga_controller_integration_tb \
    cga_controller_integration_tb.sv \
    ../Quartus/rtl/CGA/cgacard.sv \
    ../Quartus/rtl/CGA/cga.sv \
    ../Quartus/rtl/CGA/cga_pixel.sv \
    ../Quartus/rtl/CGA/cga_sequencer.sv \
    ../Quartus/rtl/CGA/cga_attrib.sv \
    ../Quartus/rtl/CGA/cga_vgaport.sv \
    ../Quartus/rtl/CGA/UM6845R.sv \
    ../Quartus/rtl/CGA/vram.sv \
    ../Quartus/rtl/CGA/busConverter.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

COMPILE_RESULT=${PIPESTATUS[0]}

if [ $COMPILE_RESULT -ne 0 ]; then
    echo ""
    echo -e "${RED}Compilation failed!${NC}"
    echo "Check $RESULTS_DIR/compile.log for details"
    echo ""
    echo "Showing compilation errors:"
    grep -i "error\|sorry" "$RESULTS_DIR/compile.log" | head -20
    exit 1
fi

echo ""
echo "================================================================"
echo "Running CGA Controller Integration Test"
echo "================================================================"
echo ""

# Run simulation
cd "$RESULTS_DIR"
./cga_controller_integration_tb 2>&1 | tee simulation.log
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
elif grep -q "*** ALL CGA CONTROLLER TESTS PASSED ***" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${GREEN}✓✓✓ SUCCESS: All CGA controller tests passed! ✓✓✓${NC}"
    exit 0
else
    echo ""
    echo -e "${YELLOW}⚠ WARNING: Could not determine test status${NC}"
    exit 1
fi
