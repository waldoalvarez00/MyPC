#!/bin/bash
# Test script for FPU I/O Port data transfer

set -e

echo "=========================================="
echo "FPU I/O Port Data Transfer Test"
echo "=========================================="

# Check for iverilog
if ! command -v iverilog &> /dev/null; then
    echo "ERROR: iverilog not found"
    echo "Please install Icarus Verilog:"
    echo "  sudo apt-get install -y iverilog"
    echo "or use local install as documented in CLAUDE.md"
    exit 1
fi

echo "Compiling FPU I/O Port testbench..."

# Compile the design
iverilog -g2012 -DSIMULATION \
    -o /tmp/tb_fpu_io_port.vvp \
    ../Quartus/rtl/FPU8087/FPU_IO_Port.sv \
    tb_fpu_io_port.sv

if [ $? -ne 0 ]; then
    echo "✗ Compilation FAILED"
    exit 1
fi

echo "Compilation successful!"
echo ""
echo "Running simulation..."
echo ""

# Run simulation
vvp /tmp/tb_fpu_io_port.vvp

if [ $? -eq 0 ]; then
    echo ""
    echo "=========================================="
    echo "✓ FPU I/O Port Test PASSED"
    echo "=========================================="
    exit 0
else
    echo ""
    echo "=========================================="
    echo "✗ FPU I/O Port Test FAILED"
    echo "=========================================="
    exit 1
fi
