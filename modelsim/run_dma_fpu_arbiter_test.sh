#!/bin/bash
# Test script for PipelinedDMAFPUArbiter

echo "========================================="
echo "PipelinedDMAFPUArbiter Integration Test"
echo "========================================="

# Clean up previous test artifacts
rm -f tb_pipelined_dma_fpu_arbiter.vvp tb_pipelined_dma_fpu_arbiter.vcd

# Compile the testbench
echo "Compiling testbench..."
iverilog -g2012 -o tb_pipelined_dma_fpu_arbiter.vvp \
    tb_pipelined_dma_fpu_arbiter.sv \
    ../Quartus/rtl/PipelinedDMAFPUArbiter.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run the simulation
echo "Running simulation..."
vvp tb_pipelined_dma_fpu_arbiter.vvp

RESULT=$?

# Clean up
rm -f tb_pipelined_dma_fpu_arbiter.vvp tb_pipelined_dma_fpu_arbiter.vcd

if [ $RESULT -eq 0 ]; then
    echo ""
    echo "========================================="
    echo "✓ PipelinedDMAFPUArbiter Test PASSED"
    echo "========================================="
    exit 0
else
    echo ""
    echo "========================================="
    echo "✗ PipelinedDMAFPUArbiter Test FAILED"
    echo "========================================="
    exit 1
fi
