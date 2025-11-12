#!/bin/bash
# Test script for FPU I/O Registers Integration

echo "========================================="
echo "FPU I/O Registers Integration Test"
echo "========================================="

# Clean up previous test artifacts
rm -f tb_fpu_io_registers.vvp tb_fpu_io_registers.vcd

# Compile the testbench
echo "Compiling testbench..."
iverilog -g2012 -o tb_fpu_io_registers.vvp \
    tb_fpu_io_registers.v \
    ../FPUControlRegister.sv \
    ../FPUStatusRegister.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run the simulation
echo "Running simulation..."
vvp tb_fpu_io_registers.vvp

RESULT=$?

# Clean up
rm -f tb_fpu_io_registers.vvp tb_fpu_io_registers.vcd

if [ $RESULT -eq 0 ]; then
    echo ""
    echo "========================================="
    echo "✓ FPU I/O Registers Test PASSED"
    echo "========================================="
    exit 0
else
    echo ""
    echo "========================================="
    echo "✗ FPU I/O Registers Test FAILED"
    echo "========================================="
    exit 1
fi
