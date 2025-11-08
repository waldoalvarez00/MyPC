#!/bin/bash

# Cache Testbench Simulation Script

echo "================================================================"
echo "Compiling Cache Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_cache_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling Cache module and testbench..."
echo ""

# Find DPRam and BlockRam modules
DPRAM_FILE=$(find ../../Quartus/rtl -name "DPRam.sv" | head -1)
BLOCKRAM_FILE=$(find ../../Quartus/rtl -name "BlockRam.sv" | head -1)

# Compile the design
iverilog -g2012 \
    -o cache_tb \
    -Dverilator \
    -I../../Quartus/rtl \
    -I../../Quartus/rtl/common \
    ../../Quartus/rtl/common/Cache.sv \
    $DPRAM_FILE \
    $BLOCKRAM_FILE \
    ../../modelsim/cache_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running Cache Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp cache_tb 2>&1 | tee simulation.log

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
echo "  - cache_tb.vcd     : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave cache_tb.vcd"
echo ""

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 5 simulation.log | tail -6
echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED" simulation.log; then
    echo "✓✓✓ SUCCESS: All Cache tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
