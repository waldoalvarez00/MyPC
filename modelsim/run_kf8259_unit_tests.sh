#!/bin/bash
#================================================================
# KF8259 Unit Tests Runner
# Runs all KF8259 submodule unit tests
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

echo -e "${BLUE}================================================================${NC}"
echo -e "${BLUE}KF8259 Unit Tests${NC}"
echo -e "${BLUE}================================================================${NC}"

# Change to script directory
cd "$(dirname "$0")"

# Test counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Function to run a unit test
run_unit_test() {
    local test_name=$1
    local test_file=$2
    local modules="${@:3}"

    echo ""
    echo -e "${BLUE}----------------------------------------------------------------${NC}"
    echo -e "${BLUE}Running: $test_name${NC}"
    echo -e "${BLUE}----------------------------------------------------------------${NC}"

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    # Compile
    iverilog -g2012 -o ${test_name}.vvp \
        -I../Quartus/rtl/KF8259 \
        ../Quartus/rtl/KF8259/KF8259_Common_Package.svh \
        $modules \
        $test_file

    if [ $? -ne 0 ]; then
        echo -e "${RED}[FAIL] Compilation failed${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi

    # Run
    vvp ${test_name}.vvp
    local exit_code=$?

    # Cleanup
    rm -f ${test_name}.vvp

    if [ $exit_code -eq 0 ]; then
        echo -e "${GREEN}[PASS] $test_name${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        return 0
    else
        echo -e "${RED}[FAIL] $test_name${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi
}

# Run unit tests
run_unit_test "Bus_Control_Logic" \
    "kf8259_bus_control_tb.sv" \
    "../Quartus/rtl/KF8259/KF8259_Bus_Control_Logic.sv"

run_unit_test "Interrupt_Request" \
    "kf8259_interrupt_request_tb.sv" \
    "../Quartus/rtl/KF8259/KF8259_Interrupt_Request.sv"

run_unit_test "Priority_Resolver" \
    "kf8259_priority_resolver_tb.sv" \
    "../Quartus/rtl/KF8259/KF8259_Priority_Resolver.sv"

run_unit_test "In_Service" \
    "kf8259_in_service_tb.sv" \
    "../Quartus/rtl/KF8259/KF8259_In_Service.sv"

# Summary
echo ""
echo -e "${BLUE}================================================================${NC}"
echo -e "${BLUE}UNIT TEST SUMMARY${NC}"
echo -e "${BLUE}================================================================${NC}"
echo "Total Tests:  $TOTAL_TESTS"
echo -e "${GREEN}Passed:       $PASSED_TESTS${NC}"
echo -e "${RED}Failed:       $FAILED_TESTS${NC}"
echo ""

if [ $FAILED_TESTS -eq 0 ]; then
    echo -e "${GREEN}✓✓✓ ALL UNIT TESTS PASSED ✓✓✓${NC}"
    exit 0
else
    echo -e "${RED}✗✗✗ SOME UNIT TESTS FAILED ✗✗✗${NC}"
    exit 1
fi
