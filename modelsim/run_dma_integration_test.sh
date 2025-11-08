#!/bin/bash

# DMA Integration Verification Test Script

echo "================================================================"
echo "DMA Integration Verification Test"
echo "================================================================"
echo ""

# Create output directory
RESULT_DIR="sim_results_dma_integration_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo "Compiling DMA integration verification testbench..."
echo ""

# Compile simple testbench (no actual simulation, just verification)
iverilog -g2012 \
    -o dma_integration_tb \
    ../../modelsim/dma_integration_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo "================================================================"
echo "Running Integration Verification"
echo "================================================================"
echo ""

# Run verification
vvp dma_integration_tb 2>&1 | tee verification.log

# Check result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Verification failed! See verification.log for details."
    exit 1
fi

echo ""
echo "Results saved to: $RESULT_DIR"
echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED" verification.log; then
    echo "✓✓✓ SUCCESS: DMA integration verified! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Check verification.log for details."
    exit 1
fi
