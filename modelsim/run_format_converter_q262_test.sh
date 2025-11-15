#!/bin/bash

# Script to run Format Converter Q2.62 mode testbench with Icarus Verilog

# Set PATH to include Icarus Verilog if installed locally
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

echo "========================================="
echo "Format Converter Q2.62 Mode Test"
echo "========================================="

# Clean up old files
rm -f format_converter_q262_tb.vvp
rm -f format_converter_q262_tb.vcd

# Compile the testbench
echo "Compiling testbench..."
iverilog -g2012 \
    -o format_converter_q262_tb.vvp \
    -s format_converter_q262_tb \
    ../Quartus/rtl/FPU8087/FPU_Format_Converter_Unified.v \
    format_converter_q262_tb.sv

if [ $? -ne 0 ]; then
    echo -e "${RED}Compilation failed!${NC}"
    exit 1
fi

echo "Compilation successful."
echo ""

# Run the simulation
echo "Running simulation..."
vvp format_converter_q262_tb.vvp

# Check result
if [ $? -eq 0 ]; then
    echo ""
    echo -e "${GREEN}=========================================${NC}"
    echo -e "${GREEN}Format Converter Q2.62 Test PASSED${NC}"
    echo -e "${GREEN}=========================================${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}=========================================${NC}"
    echo -e "${RED}Format Converter Q2.62 Test FAILED${NC}"
    echo -e "${RED}=========================================${NC}"
    exit 1
fi
