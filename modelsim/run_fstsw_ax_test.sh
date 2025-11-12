#!/bin/bash

# FSTSW AX Microcode Implementation Test
# Tests the authentic 8087 microcode-based FPU status word access

echo "=============================================="
echo "FSTSW AX Microcode Implementation Test"
echo "=============================================="
echo ""

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
    exit 1
fi

# Clean up old files
rm -f tb_fstsw_ax.vvp tb_fstsw_ax.vcd

echo "Compiling FSTSW AX testbench..."
iverilog -g2012 -o tb_fstsw_ax.vvp tb_fstsw_ax.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""
echo "Running simulation..."
echo ""

# Run simulation
vvp tb_fstsw_ax.vvp

RESULT=$?

echo ""
if [ $RESULT -eq 0 ]; then
    echo "=============================================="
    echo "TEST PASSED"
    echo "=============================================="
    exit 0
else
    echo "=============================================="
    echo "TEST FAILED"
    echo "=============================================="
    exit 1
fi
