#!/bin/bash
# Test script for Payne-Hanek dispatch logic

echo "========================================="
echo "Payne-Hanek Dispatch Logic Test"
echo "========================================="

# Setup iverilog if not in PATH
if ! command -v iverilog &> /dev/null; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Compile the design
iverilog -g2009 \
    -o payne_hanek_dispatch_test \
    -s tb_payne_hanek_dispatch \
    tb_payne_hanek_dispatch.v \
    ../FPU_Payne_Hanek.v

# Check compilation
if [ $? -ne 0 ]; then
    echo "✗ Compilation failed"
    exit 1
fi

echo "✓ Compilation successful"
echo ""

# Run simulation
./payne_hanek_dispatch_test

# Check result
if [ $? -eq 0 ]; then
    echo ""
    echo "✓ Dispatch test completed"
    exit 0
else
    echo ""
    echo "✗ Dispatch test failed"
    exit 1
fi
