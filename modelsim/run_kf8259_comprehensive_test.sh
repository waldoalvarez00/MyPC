#!/bin/bash
#================================================================
# KF8259 Comprehensive Test Runner
# Tests full KF8259 integration
#================================================================

# Add local iverilog to PATH if available
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}================================================================${NC}"
echo -e "${BLUE}KF8259 Comprehensive Integration Test${NC}"
echo -e "${BLUE}================================================================${NC}"

# Change to script directory
cd "$(dirname "$0")"

# Clean previous build
rm -f kf8259_comprehensive_test kf8259_comprehensive_test.vvp

# Compile
echo "Compiling testbench..."
iverilog -g2012 -o kf8259_comprehensive_test.vvp \
    -I../Quartus/rtl/KF8259 \
    ../Quartus/rtl/KF8259/KF8259_Common_Package.svh \
    ../Quartus/rtl/KF8259/KF8259_Bus_Control_Logic.sv \
    ../Quartus/rtl/KF8259/KF8259_Interrupt_Request.sv \
    ../Quartus/rtl/KF8259/KF8259_Priority_Resolver.sv \
    ../Quartus/rtl/KF8259/KF8259_In_Service.sv \
    ../Quartus/rtl/KF8259/KF8259_Control_Logic.sv \
    ../Quartus/rtl/KF8259/KF8259.sv \
    kf8259_comprehensive_tb.sv

if [ $? -ne 0 ]; then
    echo -e "${RED}COMPILATION FAILED${NC}"
    exit 1
fi

echo -e "${GREEN}Compilation successful${NC}"

# Run simulation
echo ""
echo "Running simulation..."
vvp kf8259_comprehensive_test.vvp

EXIT_CODE=$?

# Cleanup
rm -f kf8259_comprehensive_test.vvp

if [ $EXIT_CODE -eq 0 ]; then
    echo -e "\n${GREEN}✓✓✓ TEST PASSED ✓✓✓${NC}"
else
    echo -e "\n${RED}✗✗✗ TEST FAILED ✗✗✗${NC}"
fi

exit $EXIT_CODE
