#!/bin/bash
# Test script for pipelined arbiters
# Tests both PipelinedDMAArbiter and PipelinedMemArbiterExtend

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "========================================"
echo "Pipelined Arbiters Test Suite"
echo "========================================"
echo ""

# Check if iverilog is installed
if ! command -v iverilog &> /dev/null; then
    echo -e "${RED}ERROR: iverilog not found${NC}"
    echo "Please install Icarus Verilog:"
    echo "  Ubuntu/Debian: sudo apt-get install iverilog"
    echo "  macOS: brew install icarus-verilog"
    exit 1
fi

# Create output directory
mkdir -p sim_output

# Test 1: PipelinedDMAArbiter
echo -e "${YELLOW}Test 1: PipelinedDMAArbiter${NC}"
echo "Compiling..."

iverilog -g2012 \
    -o sim_output/pipelined_dma_arbiter_sim \
    -s pipelined_dma_arbiter_tb \
    ../Quartus/rtl/PipelinedDMAArbiter.sv \
    pipelined_dma_arbiter_tb.sv

if [ $? -eq 0 ]; then
    echo -e "${GREEN}Compilation successful${NC}"
    echo "Running simulation..."

    cd sim_output
    ./pipelined_dma_arbiter_sim
    RESULT=$?
    cd ..

    if [ $RESULT -eq 0 ]; then
        echo -e "${GREEN}✓ PipelinedDMAArbiter: ALL TESTS PASSED${NC}"
    else
        echo -e "${RED}✗ PipelinedDMAArbiter: TESTS FAILED${NC}"
        exit 1
    fi
else
    echo -e "${RED}✗ Compilation failed${NC}"
    exit 1
fi

echo ""

# Test 2: PipelinedMemArbiterExtend
echo -e "${YELLOW}Test 2: PipelinedMemArbiterExtend${NC}"
echo "Compiling..."

iverilog -g2012 \
    -o sim_output/pipelined_mem_arbiter_extend_sim \
    -s pipelined_mem_arbiter_extend_tb \
    ../Quartus/rtl/PipelinedMemArbiterExtend.sv \
    pipelined_mem_arbiter_extend_tb.sv

if [ $? -eq 0 ]; then
    echo -e "${GREEN}Compilation successful${NC}"
    echo "Running simulation..."

    cd sim_output
    ./pipelined_mem_arbiter_extend_sim
    RESULT=$?
    cd ..

    if [ $RESULT -eq 0 ]; then
        echo -e "${GREEN}✓ PipelinedMemArbiterExtend: ALL TESTS PASSED${NC}"
    else
        echo -e "${RED}✗ PipelinedMemArbiterExtend: TESTS FAILED${NC}"
        exit 1
    fi
else
    echo -e "${RED}✗ Compilation failed${NC}"
    exit 1
fi

echo ""
echo "========================================"
echo -e "${GREEN}ALL PIPELINED ARBITER TESTS PASSED${NC}"
echo "========================================"
echo ""
echo "Performance Summary:"
echo "  - PipelinedDMAArbiter: See simulation output above"
echo "  - PipelinedMemArbiterExtend: See simulation output above"
echo ""
echo "Expected Performance:"
echo "  - Throughput: >= 0.85 ops/cycle sustained"
echo "  - Latency: <= 4 cycles average"
echo "  - Back-to-back operations with no idle cycles"
echo ""
