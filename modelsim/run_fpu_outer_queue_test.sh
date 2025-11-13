#!/bin/bash
# Test script for FPU Outer Queue

echo "==========================================="
echo "FPU Outer Queue Test"
echo "==========================================="

# Clean previous build
rm -f tb_fpu_outer_queue tb_fpu_outer_queue.vcd

# Compile FPU RTL files
echo "Compiling FPU Outer Queue..."
iverilog -g2012 -o tb_fpu_outer_queue \
    -I../Quartus/rtl/FPU8087 \
    tb_fpu_outer_queue.sv \
    ../Quartus/rtl/FPU8087/FPU_Outer_Queue.v

if [ $? -ne 0 ]; then
    echo "Compilation FAILED!"
    exit 1
fi

echo "Compilation successful!"
echo ""
echo "Running simulation..."
echo ""

# Run simulation
vvp tb_fpu_outer_queue

# Check result
if [ $? -eq 0 ]; then
    echo ""
    echo "==========================================="
    echo "TEST PASSED"
    echo "==========================================="
    exit 0
else
    echo ""
    echo "==========================================="
    echo "TEST FAILED"
    echo "==========================================="
    exit 1
fi
