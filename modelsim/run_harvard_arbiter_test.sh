#!/bin/bash
#================================================================
# HarvardArbiter Unit Test Runner
# Tests arbitration between I-cache and D-cache
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
echo -e "${BLUE}HarvardArbiter Unit Test${NC}"
echo -e "${BLUE}================================================================${NC}"

# Change to script directory
cd "$(dirname "$0")"

# Clean previous build
rm -f harvard_arbiter_test harvard_arbiter_test.vvp

# Compile
echo "Compiling testbench..."
iverilog -g2012 -o harvard_arbiter_test.vvp \
    -I../Quartus/rtl/common \
    ../Quartus/rtl/common/HarvardArbiter.sv \
    harvard_arbiter_tb.sv

if [ $? -ne 0 ]; then
    echo -e "${RED}COMPILATION FAILED${NC}"
    exit 1
fi

echo -e "${GREEN}Compilation successful${NC}"

# Run simulation
echo ""
echo "Running simulation..."
vvp harvard_arbiter_test.vvp

EXIT_CODE=$?

# Cleanup
rm -f harvard_arbiter_test.vvp

if [ $EXIT_CODE -eq 0 ]; then
    echo -e "\n${GREEN}✓✓✓ TEST PASSED ✓✓✓${NC}"
else
    echo -e "\n${RED}✗✗✗ TEST FAILED ✗✗✗${NC}"
fi

exit $EXIT_CODE
