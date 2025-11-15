#!/bin/bash

# Script to run CORDIC Debug Testbench with Icarus Verilog

# Set PATH to include Icarus Verilog if installed locally
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

# Colors for output
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}=========================================${NC}"
echo -e "${BLUE}CORDIC Debug Testbench${NC}"
echo -e "${BLUE}=========================================${NC}"

# Clean up old files
rm -f cordic_debug.vvp
rm -f cordic_debug.vcd

# Compile the testbench
echo "Compiling debug testbench..."
iverilog -g2012 \
    -o cordic_debug.vvp \
    -s cordic_debug_tb \
    ../Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v \
    ../Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v \
    ../Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v \
    ../Quartus/rtl/FPU8087/FPU_Atan_Table.v \
    ../Quartus/rtl/FPU8087/FPU_Range_Reduction.v \
    ../Quartus/rtl/FPU8087/FPU_Payne_Hanek.v \
    cordic_debug_tb.sv

if [ $? -ne 0 ]; then
    echo "Compilation failed!"
    exit 1
fi

echo "Compilation successful."
echo ""

# Run the simulation
echo "Running debug simulation..."
echo "(Output will show detailed state transitions and arithmetic operations)"
echo ""
vvp cordic_debug.vvp

echo ""
echo "VCD waveform saved to: cordic_debug.vcd"
echo "(View with: gtkwave cordic_debug.vcd)"
