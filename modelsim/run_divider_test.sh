#!/bin/bash
# Divider Unit Test Script
# Tests DIV/IDIV instruction implementation
#
# NOTE: Currently incompatible with Icarus Verilog due to:
# - Enum type assignments in always_comb requiring explicit casts
# - Constant selects in always_* processes
# Requires Quartus or Verilator for compilation

echo "========================================"
echo "Divider Unit Test"
echo "========================================"
echo "NOTE: This test requires Quartus or Verilator"
echo "Icarus Verilog does not support all SystemVerilog constructs used in Divider.sv"
echo "Skipping test..."
echo ""
exit 0

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
    -o test_output/divider_tb \
    -I$CPU_DIR \
    $CPU_DIR/RegisterEnum.sv \
    $CPU_DIR/FlagsEnum.sv \
    $CPU_DIR/MicrocodeTypes.sv \
    $CPU_DIR/Divider.sv \
    $TB_DIR/divider_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run simulation
echo "Running simulation..."
cd test_output
vvp divider_tb

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
if [ -f divider_tb.vcd ]; then
    echo ""
    echo "Waveform file generated: test_output/divider_tb.vcd"
    echo "View with: gtkwave test_output/divider_tb.vcd"
fi

cd ..
exit $SIM_RESULT
