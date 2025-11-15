#!/bin/bash
# Test runner for BIOS Upload Integration test (end-to-end)

set -e

echo "=========================================="
echo "BIOS Upload Integration Test (End-to-End)"
echo "=========================================="

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Check if iverilog is installed
if ! command -v iverilog &> /dev/null; then
    echo -e "${RED}ERROR: iverilog not found${NC}"
    echo "Please install Icarus Verilog:"
    echo "  sudo apt-get install iverilog"
    exit 1
fi

# Create output directory
mkdir -p test_output

# Compile the design
echo "Compiling BIOS Upload Integration..."
iverilog -g2012 \
    -o test_output/bios_upload_integration_test \
    -I../Quartus/rtl \
    -I../Quartus/rtl/bios \
    altsyncram_sim.v \
    ../Quartus/rtl/bios/BIOSUploadController.sv \
    ../Quartus/rtl/bios/BIOS.sv \
    bios_upload_integration_tb.sv

if [ $? -ne 0 ]; then
    echo -e "${RED}✗ Compilation failed${NC}"
    exit 1
fi

echo -e "${GREEN}✓ Compilation successful${NC}"

# Run the simulation
echo ""
echo "Running simulation..."
cd test_output
vvp bios_upload_integration_test

# Check result
if [ $? -eq 0 ]; then
    echo ""
    echo -e "${GREEN}✓ Test completed${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}✗ Test failed${NC}"
    exit 1
fi
