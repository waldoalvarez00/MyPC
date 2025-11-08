#!/bin/bash
# Run VGARegisters (MCGA Controller) testbench

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Create results directory with timestamp
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_DIR="sim_results_vga_$TIMESTAMP"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling VGARegisters (MCGA Controller) Testbench"
echo "================================================================"
echo ""

# Find all required VGA files
echo "Compiling VGA controller and testbench..."
echo ""

iverilog -g2012 -DICARUS \
    -o "$RESULTS_DIR/vga_registers_tb" \
    -s vga_registers_tb \
    -I../Quartus/rtl/VGA \
    -I../Quartus/rtl/CPU/cdc \
    ../Quartus/rtl/VGA/VGARegisters.sv \
    ../Quartus/rtl/VGA/VGATypes.sv \
    DACRam_sim.sv \
    ../Quartus/rtl/CPU/cdc/BitSync.sv \
    ../Quartus/rtl/CPU/cdc/BusSync.sv \
    ../Quartus/rtl/CPU/cdc/MCP.sv \
    ../Quartus/rtl/CPU/cdc/SyncPulse.sv \
    vga_registers_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo -e "${RED}Compilation failed!${NC}"
    echo "Check $RESULTS_DIR/compile.log for details"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running VGARegisters Simulation"
echo "================================================================"
echo ""

# Run simulation
cd "$RESULTS_DIR"
./vga_registers_tb 2>&1 | tee simulation.log
SIM_RESULT=${PIPESTATUS[0]}
cd ..

# Move VCD file to results directory
if [ -f vga_registers_tb.vcd ]; then
    mv vga_registers_tb.vcd "$RESULTS_DIR/"
fi

echo ""
echo "================================================================"
echo "Simulation Complete"
echo "================================================================"
echo ""
echo "Results saved to: $RESULTS_DIR"
echo ""
echo "Generated files:"
echo "  - compile.log         : Compilation messages"
echo "  - simulation.log      : Simulation output and test results"
echo "  - vga_registers_tb.vcd : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave vga_registers_tb.vcd"
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
elif grep -q "*** ALL VGA/MCGA REGISTER TESTS PASSED ***" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo -e "${GREEN}✓✓✓ SUCCESS: All VGA/MCGA register tests passed! ✓✓✓${NC}"
    echo ""
    echo "Missing Modes (as reported by testbench):"
    grep -A 4 "MISSING VIDEO MODES" "$RESULTS_DIR/simulation.log" | tail -4
    exit 0
else
    echo ""
    echo -e "${YELLOW}⚠ WARNING: Could not determine test status${NC}"
    exit 1
fi
