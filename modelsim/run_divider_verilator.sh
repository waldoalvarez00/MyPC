#!/bin/bash
# Divider Unit Test Script (Verilator version)
# Tests DIV/IDIV instruction implementation with Verilator

echo "========================================"
echo "Divider Unit Test (Verilator)"
echo "========================================"

# Add Verilator to PATH
export PATH="/tmp/verilator_extract/usr/bin:$PATH"
export VERILATOR_ROOT="/tmp/verilator_extract/usr"

# Change to script directory
cd "$(dirname "$0")"

# Build and run with Verilator
echo "Building with Verilator..."
make -f Makefile.divider clean
make -f Makefile.divider all

if [ $? -ne 0 ]; then
    echo "ERROR: Build failed!"
    exit 1
fi

echo ""
echo "Running tests..."
make -f Makefile.divider run

SIM_RESULT=$?

# Check results
echo ""
if [ $SIM_RESULT -eq 0 ]; then
    echo "========================================"
    echo "SIMULATION PASSED!"
    echo "========================================"
else
    echo "========================================"
    echo "SIMULATION FAILED!"
    echo "========================================"
fi

exit $SIM_RESULT
