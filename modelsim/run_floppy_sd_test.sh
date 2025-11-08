#!/bin/bash

# Floppy SD Card Integration Testbench Simulation Script

echo "================================================================"
echo "Compiling Floppy SD Card Integration Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_floppy_sd_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling floppy disk manager and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o floppy_sd_integration_tb \
    -I../../Quartus/rtl \
    -I../../Quartus/rtl/Floppy \
    ../../Quartus/rtl/Floppy/floppy_disk_manager.sv \
    ../../modelsim/floppy_sd_integration_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running Floppy SD Card Integration Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp floppy_sd_integration_tb 2>&1 | tee simulation.log

# Check simulation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Simulation failed! See simulation.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Simulation Complete"
echo "================================================================"
echo ""
echo "Results saved to: $RESULT_DIR"
echo ""
echo "Generated files:"
echo "  - compile.log      : Compilation messages"
echo "  - simulation.log   : Simulation output and test results"
echo "  - floppy_sd_integration_tb.vcd : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave floppy_sd_integration_tb.vcd"
echo ""

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 5 simulation.log | tail -6
echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED" simulation.log; then
    echo "✓✓✓ SUCCESS: All Floppy SD Card Integration tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
