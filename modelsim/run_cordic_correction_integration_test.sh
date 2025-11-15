#!/bin/bash

# Script to run CORDIC Correction Integration Test with Icarus Verilog

# Set PATH to include Icarus Verilog if installed locally
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}=========================================${NC}"
echo -e "${BLUE}CORDIC Correction Integration Test${NC}"
echo -e "${BLUE}Plan 2: Heavy Unit Reuse${NC}"
echo -e "${BLUE}=========================================${NC}"

# Clean up old files
rm -f cordic_correction_integration_tb.vvp
rm -f cordic_correction_integration_tb.vcd

# Compile the testbench
echo "Compiling testbench with dependencies..."
iverilog -g2012 \
    -o cordic_correction_integration_tb.vvp \
    -s cordic_correction_integration_tb \
    ../Quartus/rtl/FPU8087/FPU_CORDIC_Wrapper.v \
    ../Quartus/rtl/FPU8087/FPU_IEEE754_AddSub.v \
    ../Quartus/rtl/FPU8087/FPU_IEEE754_MulDiv_Unified.v \
    ../Quartus/rtl/FPU8087/FPU_Atan_Table.v \
    ../Quartus/rtl/FPU8087/FPU_Range_Reduction.v \
    ../Quartus/rtl/FPU8087/FPU_Payne_Hanek.v \
    cordic_correction_integration_tb.sv

if [ $? -ne 0 ]; then
    echo -e "${RED}Compilation failed!${NC}"
    exit 1
fi

echo "Compilation successful."
echo ""

# Run the simulation
echo "Running simulation..."
echo "(This may take a while due to correction sequence...)"
echo ""
vvp cordic_correction_integration_tb.vvp

# Check result
if [ $? -eq 0 ]; then
    echo ""
    echo -e "${GREEN}=========================================${NC}"
    echo -e "${GREEN}CORDIC Correction Integration Test PASSED${NC}"
    echo -e "${GREEN}=========================================${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}=========================================${NC}"
    echo -e "${RED}CORDIC Correction Integration Test FAILED${NC}"
    echo -e "${RED}=========================================${NC}"
    exit 1
fi
