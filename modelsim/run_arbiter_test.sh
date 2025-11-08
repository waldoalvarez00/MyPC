#!/bin/bash

# Memory Arbiter Test Script

echo "================================================================"
echo "Compiling Memory Arbiter Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_arbiter_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling MemArbiter and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o arbiter_tb \
    -Dverilator \
    -I../../Quartus/rtl \
    -I../../Quartus/rtl/CPU \
    ../../Quartus/rtl/CPU/MemArbiter.sv \
    ../../modelsim/mem_arbiter_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running MemArbiter Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp arbiter_tb 2>&1 | tee simulation.log

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
echo ""

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 6 simulation.log | tail -7
echo ""

# Check if all tests passed
if grep -q "SUCCESS: All MemArbiter tests passed" simulation.log; then
    echo "✓✓✓ SUCCESS: All MemArbiter tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
