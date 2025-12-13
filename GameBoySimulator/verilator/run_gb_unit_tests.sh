#!/bin/bash
#
# GameBoy RTL Unit Test Runner
# Runs all unit tests and reports results
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Test list
TESTS=(
    "test_cpu_clken:CPU Clock Enable"
    "test_inc_de:Sequential ROM Byte Reads"
    "test_hdma:HDMA Controller"
    "test_boot_rom:Boot ROM Control"
    "test_ext_bus:External Bus Arbitration"
    "test_oam_dma:OAM DMA Engine"
    "test_memory_banking:Memory Banking"
    "test_interrupts:Interrupt Timing"
    "test_video_output:Video Output"
    "test_gui_raster_sanity:GUI Raster Sanity"
    "test_audio:Audio Output"
)

# Track results
PASSED=0
FAILED=0
TOTAL=${#TESTS[@]}

echo "=========================================="
echo "GameBoy RTL Unit Test Suite"
echo "=========================================="
echo ""

# Check if tests are built
if [ ! -d "obj_dir" ]; then
    echo -e "${YELLOW}Building tests first...${NC}"
    ./verilate_gameboy.sh --build-tests
fi

# Run each test
for test_entry in "${TESTS[@]}"; do
    test_name="${test_entry%%:*}"
    test_desc="${test_entry#*:}"

    echo "----------------------------------------"
    echo "Running: $test_desc ($test_name)"
    echo "----------------------------------------"

    # Check if test executable exists
    if [ ! -f "obj_dir/${test_name}" ]; then
        echo -e "${YELLOW}Test not built, run './verilate_gameboy.sh --build-tests' first${NC}"
        echo -e "${RED}[SKIP] $test_desc - not built${NC}"
        continue
    fi

    # Run test
    if ./obj_dir/${test_name}; then
        echo -e "${GREEN}[PASS] $test_desc${NC}"
        PASSED=$((PASSED + 1))
    else
        echo -e "${RED}[FAIL] $test_desc${NC}"
        FAILED=$((FAILED + 1))
    fi
    echo ""
done

# Summary
echo "=========================================="
echo "TEST SUMMARY"
echo "=========================================="
echo "Total:  $TOTAL"
echo -e "Passed: ${GREEN}$PASSED${NC}"
echo -e "Failed: ${RED}$FAILED${NC}"
echo ""

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}=== ALL TESTS PASSED ===${NC}"
    exit 0
else
    echo -e "${RED}=== $FAILED TEST(S) FAILED ===${NC}"
    exit 1
fi
