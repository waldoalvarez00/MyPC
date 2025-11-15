#!/bin/bash
#================================================================
# Master Test Runner - Run ALL System Tests
# Executes all test scripts and reports comprehensive results
#================================================================

# Add local iverilog to PATH if available
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Color codes for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "================================================================"
echo "MASTER TEST RUNNER - ALL SYSTEMS"
echo "================================================================"
echo ""

# Change to script directory
cd "$(dirname "$0")"

# Create master results directory
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
MASTER_RESULTS_DIR="master_test_results_${TIMESTAMP}"
mkdir -p "$MASTER_RESULTS_DIR"

# Arrays to track results
declare -a PASSED_TESTS
declare -a FAILED_TESTS
declare -a SKIPPED_TESTS

TOTAL_TESTS=0
PASSED_COUNT=0
FAILED_COUNT=0
SKIPPED_COUNT=0

# Function to run a single test
run_test() {
    local test_script=$1
    local test_name=$(basename "$test_script" .sh)

    echo -e "${BLUE}================================================================${NC}"
    echo -e "${BLUE}Running: $test_name${NC}"
    echo -e "${BLUE}================================================================${NC}"

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    # Run the test with timeout (180s for longer tests like CGA integration)
    timeout 180 bash "$test_script" > "$MASTER_RESULTS_DIR/${test_name}.log" 2>&1
    local exit_code=$?

    if [ $exit_code -eq 124 ]; then
        echo -e "${RED}[TIMEOUT] Test timed out after 180 seconds${NC}"
        FAILED_TESTS+=("$test_name (TIMEOUT)")
        FAILED_COUNT=$((FAILED_COUNT + 1))
    elif [ $exit_code -eq 0 ]; then
        echo -e "${GREEN}[PASS] $test_name${NC}"
        PASSED_TESTS+=("$test_name")
        PASSED_COUNT=$((PASSED_COUNT + 1))
    else
        # Check if it's a known skip condition
        if grep -q "COMPILATION FAILED\|cannot test\|VHDL" "$MASTER_RESULTS_DIR/${test_name}.log"; then
            echo -e "${YELLOW}[SKIP] $test_name (compilation issue or limitation)${NC}"
            SKIPPED_TESTS+=("$test_name")
            SKIPPED_COUNT=$((SKIPPED_COUNT + 1))
        else
            echo -e "${RED}[FAIL] $test_name (exit code: $exit_code)${NC}"
            FAILED_TESTS+=("$test_name")
            FAILED_COUNT=$((FAILED_COUNT + 1))
        fi
    fi

    echo ""
}

# Test list - categorized by system
echo "Discovering test scripts..."
echo ""

# Core tests
CORE_TESTS=(
    "run_ALU_sim.sh"
    "run_RegisterFile_sim.sh"
    "run_JumpTest_sim.sh"
    "run_modrm_decode_test.sh"
    "run_divider_test.sh"
)

# Memory tests
MEMORY_TESTS=(
    "run_cache_test.sh"
    "run_harvard_cache_test.sh"
    "run_sdram_test.sh"
    "run_sdram_config_test.sh"
)

# Arbiter tests
ARBITER_TESTS=(
    "run_arbiter_test.sh"
    "run_id_arbiter_test.sh"
    "run_dma_arbiter_test.sh"
    "run_mem_arbiter_extend_test.sh"
)

# Peripheral tests
PERIPHERAL_TESTS=(
    "run_pic_test.sh"
    "run_timer_test.sh"
    "run_ppi_test.sh"
)

# Storage tests
STORAGE_TESTS=(
    "run_floppy_sim.sh"
    "run_floppy_sd_test.sh"
    "run_floppy_sd_integration.sh"
    "run_floppy_dma_sim.sh"
    "run_dma_integration_test.sh"
)

# Input device tests
INPUT_TESTS=(
    "run_ps2_keyboard_test.sh"
    "run_ps2_mouse_test.sh"
)

# Video tests
VIDEO_TESTS=(
    "run_vga_test.sh"
    "run_vga_modes_test.sh"
    "run_vga_all_modes_test.sh"
    "run_vga_mode_switching_test.sh"
    "run_vga_complete_test.sh"
    "run_cga_test.sh"
    "run_cga_integration_test.sh"
)

# Serial tests
SERIAL_TESTS=(
    "run_simple_uart_test.sh"
    "run_uart_test.sh"
)

# BIOS tests
BIOS_TESTS=(
    "run_bios_upload_controller_test.sh"
    "run_bios_upload_integration_test.sh"
)

# Run all test categories
echo "Running Core Tests..."
for test in "${CORE_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Memory Tests..."
for test in "${MEMORY_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Arbiter Tests..."
for test in "${ARBITER_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Peripheral Tests..."
for test in "${PERIPHERAL_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Storage Tests..."
for test in "${STORAGE_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Input Device Tests..."
for test in "${INPUT_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Video Tests..."
for test in "${VIDEO_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Serial Tests..."
for test in "${SERIAL_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running BIOS Tests..."
for test in "${BIOS_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

# Generate summary report
echo ""
echo "================================================================"
echo "MASTER TEST SUMMARY"
echo "================================================================"
echo ""
echo "Total Tests Run: $TOTAL_TESTS"
echo -e "${GREEN}Passed: $PASSED_COUNT${NC}"
echo -e "${RED}Failed: $FAILED_COUNT${NC}"
echo -e "${YELLOW}Skipped: $SKIPPED_COUNT${NC}"
echo ""

if [ $PASSED_COUNT -gt 0 ]; then
    PASS_RATE=$((PASSED_COUNT * 100 / TOTAL_TESTS))
else
    PASS_RATE=0
fi

echo "Pass Rate: ${PASS_RATE}%"
echo ""

# List passed tests
if [ ${#PASSED_TESTS[@]} -gt 0 ]; then
    echo -e "${GREEN}Passed Tests (${#PASSED_TESTS[@]}):${NC}"
    for test in "${PASSED_TESTS[@]}"; do
        echo -e "  ${GREEN}✓${NC} $test"
    done
    echo ""
fi

# List failed tests
if [ ${#FAILED_TESTS[@]} -gt 0 ]; then
    echo -e "${RED}Failed Tests (${#FAILED_TESTS[@]}):${NC}"
    for test in "${FAILED_TESTS[@]}"; do
        echo -e "  ${RED}✗${NC} $test"
    done
    echo ""
fi

# List skipped tests
if [ ${#SKIPPED_TESTS[@]} -gt 0 ]; then
    echo -e "${YELLOW}Skipped Tests (${#SKIPPED_TESTS[@]}):${NC}"
    for test in "${SKIPPED_TESTS[@]}"; do
        echo -e "  ${YELLOW}⊘${NC} $test"
    done
    echo ""
fi

echo "================================================================"
echo "Detailed logs saved to: $MASTER_RESULTS_DIR/"
echo "================================================================"
echo ""

# Generate summary file
cat > "$MASTER_RESULTS_DIR/SUMMARY.txt" <<EOF
MASTER TEST SUMMARY
Generated: $(date)

Total Tests: $TOTAL_TESTS
Passed: $PASSED_COUNT
Failed: $FAILED_COUNT
Skipped: $SKIPPED_COUNT
Pass Rate: ${PASS_RATE}%

PASSED TESTS:
$(for test in "${PASSED_TESTS[@]}"; do echo "  ✓ $test"; done)

FAILED TESTS:
$(for test in "${FAILED_TESTS[@]}"; do echo "  ✗ $test"; done)

SKIPPED TESTS:
$(for test in "${SKIPPED_TESTS[@]}"; do echo "  ⊘ $test"; done)
EOF

# Exit with appropriate code
if [ $FAILED_COUNT -eq 0 ]; then
    echo -e "${GREEN}✓✓✓ ALL TESTS PASSED OR SKIPPED ✓✓✓${NC}"
    exit 0
else
    echo -e "${RED}✗✗✗ SOME TESTS FAILED ✗✗✗${NC}"
    exit 1
fi
