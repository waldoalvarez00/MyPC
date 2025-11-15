#!/bin/bash

echo "========================================"
echo "Microcode Unit Test"
echo "========================================"

# Check for iverilog
if ! command -v iverilog &> /dev/null; then
    echo "ERROR: iverilog not found! Please install Icarus Verilog."
    exit 1
fi

# Compile the testbench and microcode module
echo "Compiling RTL and testbench..."
iverilog -g2012 -o microcode_tb.vvp \
    -I../Quartus/rtl/CPU \
    -I../Quartus/rtl/common \
    microcode_tb.sv \
    ../Quartus/rtl/CPU/InstructionDefinitions.sv \
    ../Quartus/rtl/CPU/Fifo.sv \
    ../Quartus/rtl/common/DPRam.sv \
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
vvp microcode_tb.vvp

# Capture exit code
EXIT_CODE=$?

# Clean up
rm -f microcode_tb.vvp

# Return exit code
exit $EXIT_CODE
