#!/bin/bash

echo "================================================================"
echo "Compiling FPU Format Converter Testbench"
echo "================================================================"

# Add Icarus Verilog to PATH if installed locally
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Store the base directory
BASE_DIR="$(pwd)/.."

# Create output directory
RESULT_DIR="sim_results_fpu_format_converter_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling FPU Format Converter module and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o fpu_format_converter_tb \
    -I${BASE_DIR}/Quartus/rtl/FPU8087 \
    ${BASE_DIR}/Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v \
    ${BASE_DIR}/modelsim/fpu_format_converter_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running FPU Format Converter Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp fpu_format_converter_tb 2>&1 | tee simulation.log

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
echo "  - fpu_format_converter_tb.vcd : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave fpu_format_converter_tb.vcd"
echo ""

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 5 simulation.log

echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED" simulation.log; then
    echo "✓✓✓ SUCCESS: All FPU format converter tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
