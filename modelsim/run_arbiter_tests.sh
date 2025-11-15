#!/bin/bash
#================================================================
# Arbiter Unit Tests Runner
# Runs all arbiter unit tests
#================================================================

# Add local iverilog to PATH if available
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo ""
echo -e "${BLUE}╔════════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║                  ARBITER UNIT TESTS                            ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Change to script directory
cd "$(dirname "$0")"

OVERALL_RESULT=0

# Run HarvardArbiter test
echo -e "${YELLOW}▶ Running HarvardArbiter Unit Test...${NC}"
./run_harvard_arbiter_test.sh
HARVARD_RESULT=$?

if [ $HARVARD_RESULT -ne 0 ]; then
    OVERALL_RESULT=1
fi

echo ""
echo ""

# Run PipelinedDMAFPUArbiter test
echo -e "${YELLOW}▶ Running PipelinedDMAFPUArbiter Unit Test...${NC}"
./run_pipelined_dma_fpu_arbiter_test.sh
PIPELINED_RESULT=$?

if [ $PIPELINED_RESULT -ne 0 ]; then
    OVERALL_RESULT=1
fi

# Final summary
echo ""
echo -e "${BLUE}================================================================${NC}"
echo -e "${BLUE}ARBITER UNIT TEST SUMMARY${NC}"
echo -e "${BLUE}================================================================${NC}"

if [ $HARVARD_RESULT -eq 0 ]; then
    echo -e "HarvardArbiter:           ${GREEN}✓ PASSED${NC}"
else
    echo -e "HarvardArbiter:           ${RED}✗ FAILED${NC}"
fi

if [ $PIPELINED_RESULT -eq 0 ]; then
    echo -e "PipelinedDMAFPUArbiter:   ${GREEN}✓ PASSED${NC}"
else
    echo -e "PipelinedDMAFPUArbiter:   ${RED}✗ FAILED${NC}"
fi

echo -e "${BLUE}================================================================${NC}"

if [ $OVERALL_RESULT -eq 0 ]; then
    echo ""
    echo -e "${GREEN}╔════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║            ✓✓✓ ALL ARBITER TESTS PASSED ✓✓✓                   ║${NC}"
    echo -e "${GREEN}║                                                                ║${NC}"
    echo -e "${GREEN}║  Arbiter subsystems have new unit test coverage!              ║${NC}"
    echo -e "${GREEN}╚════════════════════════════════════════════════════════════════╝${NC}"
    echo ""
else
    echo ""
    echo -e "${RED}╔════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${RED}║              ✗✗✗ SOME TESTS FAILED ✗✗✗                        ║${NC}"
    echo -e "${RED}╚════════════════════════════════════════════════════════════════╝${NC}"
    echo ""
fi

exit $OVERALL_RESULT
