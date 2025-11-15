#!/bin/bash

echo "========================================"
echo "Prefetch Unit Test"
echo "========================================"

# Check for iverilog
if ! command -v iverilog &> /dev/null; then
    echo "ERROR: iverilog not found! Please install Icarus Verilog."
    exit 1
fi

# Compile the testbench and prefetch module
echo "Compiling RTL and testbench..."
iverilog -g2012 -o prefetch_tb.vvp \
    -I../Quartus/rtl/CPU \
    -I../Quartus/rtl/common \
    prefetch_tb.sv \
    ../Quartus/rtl/CPU/Prefetch.sv \
    2>&1

# Check if compilation succeeded
if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run the simulation
echo "Running simulation..."
vvp prefetch_tb.vvp

# Capture exit code
EXIT_CODE=$?

# Clean up
rm -f prefetch_tb.vvp

# Return exit code
exit $EXIT_CODE
