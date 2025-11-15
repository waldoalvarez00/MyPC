#!/bin/bash
# ALU Unit Test Script
# Tests arithmetic and logic unit operations

echo "========================================"
echo "ALU Unit Test"
echo "========================================"

# Add local iverilog to PATH if available
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Set paths
CPU_DIR="../Quartus/rtl/CPU"
ALU_DIR="../Quartus/rtl/CPU/alu"
TB_DIR="."

# Change to script directory
cd "$(dirname "$0")"

# Create output directory
mkdir -p test_output

# Compile with Icarus Verilog
echo "Compiling RTL and testbench..."

iverilog -g2012 -gassertions -grelative-include \
    -o test_output/alu_tb \
    -I$CPU_DIR \
    -I$ALU_DIR \
    $CPU_DIR/RegisterEnum.sv \
    $CPU_DIR/FlagsEnum.sv \
    $CPU_DIR/MicrocodeTypes.sv \
    $ALU_DIR/aaa.sv \
    $ALU_DIR/aas.sv \
    $ALU_DIR/adc.sv \
    $ALU_DIR/add.sv \
    $ALU_DIR/and.sv \
    $ALU_DIR/bound.sv \
    $ALU_DIR/daa.sv \
    $ALU_DIR/das.sv \
    $ALU_DIR/enter.sv \
    $ALU_DIR/extend.sv \
    $ALU_DIR/flags.sv \
    $ALU_DIR/mul.sv \
    $ALU_DIR/not.sv \
    $ALU_DIR/or.sv \
    $ALU_DIR/rcl.sv \
    $ALU_DIR/rcr.sv \
    $ALU_DIR/rol.sv \
    $ALU_DIR/ror.sv \
    $ALU_DIR/sar.sv \
    $ALU_DIR/shift_flags.sv \
    $ALU_DIR/shl.sv \
    $ALU_DIR/shr.sv \
    $ALU_DIR/sub.sv \
    $ALU_DIR/xor.sv \
    $ALU_DIR/ALU.sv \
    $TB_DIR/ALU_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run simulation
echo "Running simulation..."
cd test_output
vvp alu_tb

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
if [ -f alu_tb.vcd ]; then
    echo ""
    echo "Waveform file generated: test_output/alu_tb.vcd"
    echo "View with: gtkwave test_output/alu_tb.vcd"
fi

cd ..
exit $SIM_RESULT
