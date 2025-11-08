#!/bin/bash

# IDArbiter Test Script

echo "================================================================"
echo "Compiling IDArbiter Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_id_arbiter_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling IDArbiter and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o id_arbiter_tb \
    -Dverilator \
    -I../../Quartus/rtl \
    ../../Quartus/rtl/IDArbiter.sv \
    ../../modelsim/id_arbiter_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running IDArbiter Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp id_arbiter_tb 2>&1 | tee simulation.log

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

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 6 simulation.log | tail -7
echo ""

# Check if all tests passed
if grep -q "SUCCESS: All IDArbiter tests passed" simulation.log; then
    echo "✓✓✓ SUCCESS: All IDArbiter tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
