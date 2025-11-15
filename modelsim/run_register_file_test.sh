#!/bin/bash
# RegisterFile Unit Test Script
# Tests general purpose register file (AX, BX, CX, DX, etc.)

echo "========================================"
echo "RegisterFile Unit Test"
echo "========================================"

# Add local iverilog to PATH if available
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Set paths
CPU_DIR="../Quartus/rtl/CPU"
TB_DIR="."

# Change to script directory
cd "$(dirname "$0")"

# Create output directory
mkdir -p test_output

# Compile with Icarus Verilog
echo "Compiling RTL and testbench..."

iverilog -g2012 -gassertions -grelative-include \
    -o test_output/register_file_tb \
    -I$CPU_DIR \
    $CPU_DIR/RegisterEnum.sv \
    $CPU_DIR/FlagsEnum.sv \
    $CPU_DIR/MicrocodeTypes.sv \
    $CPU_DIR/RegisterFile.sv \
    $TB_DIR/RegisterFile_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run simulation
echo "Running simulation..."
cd test_output
vvp register_file_tb

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

# Display waveform info
if [ -f register_file_tb.vcd ]; then
    echo ""
    echo "Waveform file generated: test_output/register_file_tb.vcd"
    echo "View with: gtkwave test_output/register_file_tb.vcd"
fi

cd ..
exit $SIM_RESULT
