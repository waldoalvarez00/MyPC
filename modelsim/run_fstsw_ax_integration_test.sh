#!/bin/bash

# FSTSW AX Integration Validation Test
# Validates the complete implementation without runtime simulation

echo "=============================================="
echo "FSTSW AX Integration Validation"
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
rm -f tb_fstsw_ax_integration.vvp tb_fstsw_ax_integration.vcd

echo "Compiling integration validation testbench..."

# Include path for MicrocodeTypes.sv
INCLUDE_PATH="../Quartus/rtl/CPU"

iverilog -g2012 \
    -I${INCLUDE_PATH} \
    -o tb_fstsw_ax_integration.vvp \
    tb_fstsw_ax_integration.sv \
    ${INCLUDE_PATH}/MicrocodeTypes.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""
echo "Running validation..."
echo ""

# Run validation
vvp tb_fstsw_ax_integration.vvp

RESULT=$?

echo ""
if [ $RESULT -eq 0 ]; then
    echo "=============================================="
    echo "VALIDATION PASSED"
    echo "=============================================="
    exit 0
else
    echo "=============================================="
    echo "VALIDATION FAILED"
    echo "=============================================="
    exit 1
fi
