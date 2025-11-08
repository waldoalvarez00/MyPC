#!/bin/bash

# DMA Arbiter Test Script

echo "================================================================"
echo "Compiling DMA Arbiter Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_dma_arbiter_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling DMAArbiter and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o dma_arbiter_tb \
    -Dverilator \
    -I../../Quartus/rtl \
    ../../Quartus/rtl/DMAArbiter.sv \
    ../../modelsim/dma_arbiter_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running DMAArbiter Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp dma_arbiter_tb 2>&1 | tee simulation.log

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
if grep -q "SUCCESS: All DMAArbiter tests passed" simulation.log; then
    echo "✓✓✓ SUCCESS: All DMAArbiter tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
