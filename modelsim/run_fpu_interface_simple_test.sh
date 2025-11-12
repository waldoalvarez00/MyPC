#!/bin/bash
# Simplified test script for CPU-FPU interface signal generation

echo "=============================================="
echo "Simplified CPU-FPU Interface Test"
echo "=============================================="
echo ""

# Clean previous build
rm -f tb_fpu_interface_simple tb_fpu_interface_simple.vcd

# Check if iverilog is available
if ! command -v iverilog &> /dev/null; then
    echo "ERROR: iverilog not found in PATH"
    echo ""
    echo "To install iverilog locally (without sudo):"
    echo "  cd /tmp"
    echo "  apt-get download iverilog"
    echo "  dpkg-deb -x iverilog_*.deb iverilog_extract"
    echo "  cd iverilog_extract/usr"
    echo "  ln -s lib/x86_64-linux-gnu x86_64-linux-gnu"
    echo "  export PATH=\"/tmp/iverilog_extract/usr/bin:\$PATH\""
    echo ""
    echo "Or with sudo:"
    echo "  sudo apt-get install -y iverilog"
    echo ""
    exit 1
fi

# Compile testbench (standalone, no dependencies)
echo "Compiling simplified FPU interface test..."
iverilog -g2012 -o tb_fpu_interface_simple tb_fpu_interface_simple.sv

if [ $? -ne 0 ]; then
    echo "Compilation FAILED!"
    exit 1
fi

echo "Compilation successful!"
echo ""
echo "Running simulation..."
echo ""

# Run simulation
vvp tb_fpu_interface_simple

# Check result
if [ $? -eq 0 ]; then
    echo ""
    echo "=============================================="
    echo "TEST PASSED"
    echo "=============================================="
    exit 0
else
    echo ""
    echo "=============================================="
    echo "TEST FAILED"
    echo "=============================================="
    exit 1
fi
