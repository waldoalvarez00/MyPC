#!/bin/bash
#================================================================
# VGA Unit Tests Runner
# Runs all VGA submodule unit tests
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
echo -e "${BLUE}║                VGA SUBSYSTEM UNIT TESTS                        ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Change to script directory
cd "$(dirname "$0")"

OVERALL_RESULT=0

# Run VGASync test
echo -e "${YELLOW}▶ Running VGASync Unit Test...${NC}"
./run_vgasync_unit_test.sh
VGASYNC_RESULT=$?

if [ $VGASYNC_RESULT -ne 0 ]; then
    OVERALL_RESULT=1
fi

echo ""
echo ""

# Run FontColorLUT test
echo -e "${YELLOW}▶ Running FontColorLUT Unit Test...${NC}"
./run_fontcolorlut_unit_test.sh
FONTLUT_RESULT=$?

if [ $FONTLUT_RESULT -ne 0 ]; then
    OVERALL_RESULT=1
fi

# Final summary
echo ""
echo -e "${BLUE}================================================================${NC}"
echo -e "${BLUE}VGA UNIT TEST SUMMARY${NC}"
echo -e "${BLUE}================================================================${NC}"

if [ $VGASYNC_RESULT -eq 0 ]; then
    echo -e "VGASync:       ${GREEN}✓ PASSED${NC}"
else
    echo -e "VGASync:       ${RED}✗ FAILED${NC}"
fi

if [ $FONTLUT_RESULT -eq 0 ]; then
    echo -e "FontColorLUT:  ${GREEN}✓ PASSED${NC}"
else
    echo -e "FontColorLUT:  ${RED}✗ FAILED${NC}"
fi

echo -e "${BLUE}================================================================${NC}"

if [ $OVERALL_RESULT -eq 0 ]; then
    echo ""
    echo -e "${GREEN}╔════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║              ✓✓✓ ALL VGA TESTS PASSED ✓✓✓                     ║${NC}"
    echo -e "${GREEN}║                                                                ║${NC}"
    echo -e "${GREEN}║  VGA subsystem has new unit test coverage!                    ║${NC}"
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
