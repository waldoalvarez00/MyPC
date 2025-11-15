#!/bin/bash
#================================================================
# KF8259 Complete Test Suite Runner
# Runs all unit tests and integration tests
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
echo -e "${BLUE}║          KF8259 (8259A PIC) COMPLETE TEST SUITE               ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Change to script directory
cd "$(dirname "$0")"

OVERALL_RESULT=0

# Run unit tests
echo -e "${YELLOW}▶ Running Unit Tests...${NC}"
./run_kf8259_unit_tests.sh
UNIT_RESULT=$?

if [ $UNIT_RESULT -ne 0 ]; then
    OVERALL_RESULT=1
fi

echo ""
echo ""

# Run comprehensive integration test
echo -e "${YELLOW}▶ Running Comprehensive Integration Test...${NC}"
./run_kf8259_comprehensive_test.sh
INTEGRATION_RESULT=$?

if [ $INTEGRATION_RESULT -ne 0 ]; then
    OVERALL_RESULT=1
fi

# Final summary
echo ""
echo -e "${BLUE}================================================================${NC}"
echo -e "${BLUE}COMPLETE TEST SUITE SUMMARY${NC}"
echo -e "${BLUE}================================================================${NC}"

if [ $UNIT_RESULT -eq 0 ]; then
    echo -e "Unit Tests:        ${GREEN}✓ PASSED${NC}"
else
    echo -e "Unit Tests:        ${RED}✗ FAILED${NC}"
fi

if [ $INTEGRATION_RESULT -eq 0 ]; then
    echo -e "Integration Test:  ${GREEN}✓ PASSED${NC}"
else
    echo -e "Integration Test:  ${RED}✗ FAILED${NC}"
fi

echo -e "${BLUE}================================================================${NC}"

if [ $OVERALL_RESULT -eq 0 ]; then
    echo ""
    echo -e "${GREEN}╔════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║              ✓✓✓ ALL TESTS PASSED ✓✓✓                        ║${NC}"
    echo -e "${GREEN}║                                                                ║${NC}"
    echo -e "${GREEN}║  KF8259 has comprehensive test coverage and is verified!      ║${NC}"
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
