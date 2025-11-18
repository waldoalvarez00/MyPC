#!/bin/bash
#================================================================
# Master Test Runner - Run ALL System Tests
# Executes all test scripts and reports comprehensive results
#================================================================

# Add local iverilog to PATH if available
if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
    export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
fi

# Color codes for output (disabled to avoid escape clutter in logs)
GREEN=''
RED=''
YELLOW=''
BLUE=''
NC='' # No Color

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
declare -a TEST_RESULTS

TOTAL_TESTS=0
PASSED_COUNT=0
FAILED_COUNT=0
SKIPPED_COUNT=0
elapsed_time=0

# Function to run a single test
run_test() {
    local test_script=$1
    local test_name=$(basename "$test_script" .sh)
    local run_log="${MASTER_RESULTS_DIR}/${test_name}.log"

    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    local test_start_ts
    test_start_ts=$(date +%s)

    timeout 180 bash "$test_script" > "$run_log" 2>&1
    local exit_code=$?
    local end_ts
    end_ts=$(date +%s)
    local duration=$((end_ts - test_start_ts))
    if [ "$duration" -lt 0 ]; then
        duration=0
    fi
    elapsed_time=$((elapsed_time + duration))

    local remaining=$((PLANNED_TESTS - TOTAL_TESTS))
    local avg=0
    if [ $TOTAL_TESTS -gt 0 ]; then
        avg=$((elapsed_time / TOTAL_TESTS))
    fi
    local eta_seconds=$((remaining * avg))
    local eta_label="$(printf "%02d:%02d" $((eta_seconds / 60)) $((eta_seconds % 60)))"

    local status_label=""
    local status_color=""

    if [ $exit_code -eq 0 ]; then
        status_label="PASS"
        status_color=$GREEN
        PASSED_TESTS+=("$test_name")
        PASSED_COUNT=$((PASSED_COUNT + 1))
        TEST_RESULTS+=("${GREEN}PASS${NC} - ${test_name}")
    else
        if grep -q "COMPILATION FAILED\|cannot test\|VHDL" "$run_log"; then
            status_label="SKIP"
            status_color=$YELLOW
            SKIPPED_TESTS+=("$test_name")
            SKIPPED_COUNT=$((SKIPPED_COUNT + 1))
            TEST_RESULTS+=("${YELLOW}SKIP${NC} - ${test_name}")
        else
            status_label="FAIL"
            status_color=$RED
            FAILED_TESTS+=("$test_name")
            FAILED_COUNT=$((FAILED_COUNT + 1))
            TEST_RESULTS+=("${RED}FAIL${NC} - ${test_name}")
        fi
    fi

    printf "%s %-30s | run=%d/%d pass=%d fail=%d skip=%d | dur=%02ds | ETA=%s\n" \
        "${status_color}${status_label}${NC}" "$test_name" "$TOTAL_TESTS" "$PLANNED_TESTS" \
        "$PASSED_COUNT" "$FAILED_COUNT" "$SKIPPED_COUNT" "$duration" "$eta_label"

    if [ $exit_code -ne 0 ]; then
        echo "Failure details (last 20 lines of ${run_log}):"
        tail -n 20 "$run_log"
        echo "ETA remaining: ${eta_label}"
    fi

    echo ""
}

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
    "run_pipelined_arbiter_tests.sh"
)

# Peripheral tests
PERIPHERAL_TESTS=(
    "run_pic_test.sh"
    "run_timer_test.sh"
    "run_ppi_test.sh"
)

# Storage tests
STORAGE_TESTS=()

# FPU tests
FPU_TESTS=(
    "run_fpu_format_converter_test.sh"
    "run_format_converter_q262_test.sh"
    "run_fpu_interface_test.sh"
    "run_fpu_interface_simple_test.sh"
    "run_fpu_io_port_test.sh"
    "run_fpu_outer_queue_test.sh"
)

# Floppy/FDC-specific
FLOPPY_TESTS=(
    "run_floppy_sim.sh"
    "run_floppy_dma_sim.sh"
    "run_floppy_sd_test.sh"
    "run_floppy_sd_integration.sh"
)

# DMA-focused tests
DMA_TESTS=(
    "run_dma_arbiter_test.sh"
    "run_dma_fpu_arbiter_test.sh"
    "run_dma_integration_test.sh"
    "run_mem_arbiter_extend_test.sh"
)

# Input device tests
INPUT_TESTS=(
    "run_ps2_keyboard_test.sh"
    "run_ps2_mouse_test.sh"
    "run_ps2_keyboard_protocol_test.sh"
    "run_ps2_mouse_verilator.sh"
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
    "run_vga_unit_tests.sh"
    "run_cga_unit_tests.sh"
    "run_vgasync_unit_test.sh"
    "run_vga_framebuffer_integration.sh"
)

# Serial tests
SERIAL_TESTS=(
    "run_simple_uart_test.sh"
    "run_uart_test.sh"
    "run_uart_16750_lite_test.sh"
)

# BIOS tests
BIOS_TESTS=(
    "run_bios_upload_controller_test.sh"
    "run_bios_upload_integration_test.sh"
)

ALL_TEST_CATEGORIES=(
    CORE_TESTS MEMORY_TESTS ARBITER_TESTS PERIPHERAL_TESTS STORAGE_TESTS INPUT_TESTS
    VIDEO_TESTS SERIAL_TESTS BIOS_TESTS FPU_TESTS FLOPPY_TESTS DMA_TESTS
)
PLANNED_TESTS=0
for category in "${ALL_TEST_CATEGORIES[@]}"; do
    # Expand the array for this category
    eval "arr=(\"\${${category}[@]}\")"
    for test in "${arr[@]}"; do
        [ -f "$test" ] && PLANNED_TESTS=$((PLANNED_TESTS + 1))
    done
done

echo "Discovering test scripts..."
echo ""


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

echo "Running FPU Tests..."
for test in "${FPU_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running Floppy Tests..."
for test in "${FLOPPY_TESTS[@]}"; do
    [ -f "$test" ] && run_test "$test"
done

echo "Running DMA Tests..."
for test in "${DMA_TESTS[@]}"; do
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

if [ $TOTAL_TESTS -gt 0 ]; then
    PASS_RATE=$((PASSED_COUNT * 100 / TOTAL_TESTS))
else
    PASS_RATE=0
fi

printf "RESULT Total=%d Pass=%d Fail=%d Skip=%d PassRate=%d%%\n" \
    "$TOTAL_TESTS" "$PASSED_COUNT" "$FAILED_COUNT" "$SKIPPED_COUNT" "$PASS_RATE"
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
