#!/bin/bash

# KF8253 Comprehensive Testbench Simulation Script

echo "================================================================"
echo "Compiling KF8253 Comprehensive Testbench"
echo "================================================================"

# Add Icarus Verilog to PATH if installed locally
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Store the base directory
BASE_DIR="$(pwd)/.."

# Create output directory
RESULT_DIR="sim_results_kf8253_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling KF8253 module and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o kf8253_tb \
    -I${BASE_DIR}/Quartus/rtl \
    -I${BASE_DIR}/Quartus/rtl/KF8253 \
    ${BASE_DIR}/Quartus/rtl/KF8253/KF8253.sv \
    ${BASE_DIR}/Quartus/rtl/KF8253/KF8253_Counter.sv \
    ${BASE_DIR}/Quartus/rtl/KF8253/KF8253_Control_Logic.sv \
    ${BASE_DIR}/modelsim/kf8253_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running KF8253 Comprehensive Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp kf8253_tb 2>&1 | tee simulation.log

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
echo "  - kf8253_tb.vcd    : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave kf8253_tb.vcd"
echo ""

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 6 simulation.log | tail -7
echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED" simulation.log; then
    echo "✓✓✓ SUCCESS: All KF8253 tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
