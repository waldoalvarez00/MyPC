#!/bin/bash
#
# GameBoy Doctor Test Runner
# Runs all Blargg CPU instruction tests with gameboy-doctor comparison
#
# Usage:
#   ./run_all_doctor_tests.sh              # Run all tests
#   ./run_all_doctor_tests.sh 6            # Run test 6 only
#   ./run_all_doctor_tests.sh 1 3 6        # Run tests 1, 3, and 6
#

set -e
cd "$(dirname "$0")"

# Test configuration
# Maps test number to ROM file and description
declare -A TEST_ROMS=(
    [1]="test_roms/cpu_instrs/individual/01-special.gb"
    [2]="test_roms/cpu_instrs/individual/02-interrupts.gb"
    [3]="test_roms/cpu_instrs/individual/03-op sp,hl.gb"
    [4]="test_roms/cpu_instrs/individual/04-op r,imm.gb"
    [5]="test_roms/cpu_instrs/individual/05-op rp.gb"
    [6]="test_roms/cpu_instrs/individual/06-ld r,r.gb"
    [7]="test_roms/cpu_instrs/individual/07-jr,jp,call,ret,rst.gb"
    [8]="test_roms/cpu_instrs/individual/08-misc instrs.gb"
    [9]="test_roms/cpu_instrs/individual/09-op r,r.gb"
    [10]="test_roms/cpu_instrs/individual/10-bit ops.gb"
    [11]="test_roms/cpu_instrs/individual/11-op a,(hl).gb"
)

declare -A TEST_NAMES=(
    [1]="01-special"
    [2]="02-interrupts"
    [3]="03-op sp,hl"
    [4]="04-op r,imm"
    [5]="05-op rp"
    [6]="06-ld r,r"
    [7]="07-jr,jp,call,ret,rst"
    [8]="08-misc instrs"
    [9]="09-op r,r"
    [10]="10-bit ops"
    [11]="11-op a,(hl)"
)

# Default: number of instructions to log per test
DEFAULT_INSTRUCTIONS=50000

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=========================================="
echo "  GameBoy Doctor Test Runner"
echo "=========================================="
echo ""

# Check if test binary exists
if [ ! -f "obj_dir/test_doctor_compare" ]; then
    echo -e "${RED}Error: obj_dir/test_doctor_compare not found${NC}"
    echo ""
    echo "Build it with:"
    echo "  cd obj_dir"
    echo "  g++ -Os -I. -I/usr/local/share/verilator/include \\"
    echo "    -I/usr/local/share/verilator/include/vltstd \\"
    echo "    -DVM_TRACE=1 -c -o test_doctor_compare.o ../test_doctor_compare.cpp"
    echo "  g++ test_doctor_compare.o verilated.o verilated_vcd_c.o \\"
    echo "    verilated_threads.o Vtop__ALL.a -pthread -lpthread -latomic \\"
    echo "    -o test_doctor_compare"
    exit 1
fi

# Check for reference logs
TRUTH_DIR="gameboy-doctor/truth/unzipped/cpu_instrs"
if [ ! -d "$TRUTH_DIR" ]; then
    echo -e "${YELLOW}Warning: Reference logs not found at $TRUTH_DIR${NC}"
    echo "Unzipping reference logs..."
    mkdir -p "$TRUTH_DIR"
    for i in 1 2 3 4 5 6 7 8 9 10 11; do
        if [ -f "gameboy-doctor/truth/zipped/cpu_instrs/${i}.zip" ]; then
            unzip -o "gameboy-doctor/truth/zipped/cpu_instrs/${i}.zip" -d "$TRUTH_DIR/"
        fi
    done
fi

# Create logs directory
mkdir -p logs

# Determine which tests to run
if [ $# -eq 0 ]; then
    # Run all tests
    TESTS_TO_RUN=(1 2 3 4 5 6 7 8 9 10 11)
else
    # Run specified tests
    TESTS_TO_RUN=("$@")
fi

echo "Tests to run: ${TESTS_TO_RUN[*]}"
echo ""

# Track results
declare -A RESULTS
PASSED=0
FAILED=0

# Run each test
for test_num in "${TESTS_TO_RUN[@]}"; do
    rom="${TEST_ROMS[$test_num]}"
    name="${TEST_NAMES[$test_num]}"

    if [ -z "$rom" ]; then
        echo -e "${RED}Unknown test number: $test_num${NC}"
        continue
    fi

    echo "=========================================="
    echo "Test $test_num: $name"
    echo "=========================================="

    if [ ! -f "$rom" ]; then
        echo -e "${RED}ROM not found: $rom${NC}"
        RESULTS[$test_num]="SKIP"
        continue
    fi

    log_file="logs/test_${test_num}.log"
    ref_file="${TRUTH_DIR}/${test_num}.log"

    # Run simulation
    echo "Running simulation..."
    ./obj_dir/test_doctor_compare "$rom" "$log_file" "$ref_file" $DEFAULT_INSTRUCTIONS 2>&1 | tail -20

    # Run gameboy-doctor comparison
    echo ""
    echo "Running gameboy-doctor comparison..."

    result=$(python3 gameboy-doctor/gameboy-doctor "$log_file" cpu_instrs "$test_num" 2>&1 | head -30)
    echo "$result"

    # Check result
    if echo "$result" | grep -q "Mismatch"; then
        echo -e "${RED}FAILED${NC}"
        RESULTS[$test_num]="FAIL"
        ((FAILED++))
    elif echo "$result" | grep -q "match"; then
        echo -e "${GREEN}PASSED${NC}"
        RESULTS[$test_num]="PASS"
        ((PASSED++))
    else
        echo -e "${YELLOW}UNKNOWN${NC}"
        RESULTS[$test_num]="UNKNOWN"
    fi

    echo ""
done

# Summary
echo "=========================================="
echo "  Test Summary"
echo "=========================================="
echo ""

for test_num in "${TESTS_TO_RUN[@]}"; do
    name="${TEST_NAMES[$test_num]}"
    result="${RESULTS[$test_num]}"

    case $result in
        PASS)
            echo -e "  Test $test_num ($name): ${GREEN}PASSED${NC}"
            ;;
        FAIL)
            echo -e "  Test $test_num ($name): ${RED}FAILED${NC}"
            ;;
        SKIP)
            echo -e "  Test $test_num ($name): ${YELLOW}SKIPPED${NC}"
            ;;
        *)
            echo -e "  Test $test_num ($name): ${YELLOW}UNKNOWN${NC}"
            ;;
    esac
done

echo ""
echo "Total: $PASSED passed, $FAILED failed"
echo ""

# Exit with error if any tests failed
if [ $FAILED -gt 0 ]; then
    exit 1
fi
