#!/bin/bash
# Run all testbenches and generate comprehensive report

echo "========================================"
echo "Running All CPU Component Testbenches"
echo "========================================"
echo "Start Time: $(date)"
echo ""

cd "$(dirname "$0")"

# Create log directory
LOGDIR="sim_results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$LOGDIR"

total_tests=0
passed_tests=0
failed_tests=0

# Function to run a simulation and capture results
run_sim() {
    local script=$1
    local name=$2

    echo ""
    echo "========================================"
    echo "Running: $name"
    echo "========================================"

    if [ ! -f "$script" ]; then
        echo "ERROR: Script $script not found!"
        return 1
    fi

    chmod +x "$script"
    ./"$script" 2>&1 | tee "$LOGDIR/${name}.log"
    local status=${PIPESTATUS[0]}

    # Parse results from log
    local tests=$(grep "Total Tests:" "$LOGDIR/${name}.log" | awk '{print $3}')
    local passed=$(grep "Passed:" "$LOGDIR/${name}.log" | awk '{print $2}')
    local failed=$(grep "Failed:" "$LOGDIR/${name}.log" | awk '{print $2}')

    if [ -n "$tests" ]; then
        total_tests=$((total_tests + tests))
        passed_tests=$((passed_tests + passed))
        failed_tests=$((failed_tests + failed))

        if [ "$failed" -eq 0 ]; then
            echo "✓ $name: ALL TESTS PASSED ($passed/$tests)"
        else
            echo "✗ $name: SOME TESTS FAILED ($passed/$tests passed, $failed failed)"
        fi
    else
        echo "⚠ $name: Could not parse test results"
    fi

    return $status
}

#======================================
# Run CPU Component Tests
#======================================

echo ""
echo "=========================================="
echo "PART 1: CPU Component Tests"
echo "=========================================="

run_sim "run_RegisterFile_sim.sh" "RegisterFile"
run_sim "run_JumpTest_sim.sh" "JumpTest"
run_sim "run_ALU_sim.sh" "ALU"

#======================================
# Generate Summary Report
#======================================

echo ""
echo "=========================================="
echo "SIMULATION SUMMARY REPORT"
echo "=========================================="
echo "Completion Time: $(date)"
echo ""
echo "Total Components Tested: 3"
echo "Total Test Cases: $total_tests"
echo "Passed:          $passed_tests"
echo "Failed:          $failed_tests"
echo ""

if [ $failed_tests -eq 0 ]; then
    echo "OVERALL STATUS: ✓ ALL TESTS PASSED"
else
    echo "OVERALL STATUS: ✗ SOME TESTS FAILED"
fi

echo ""
echo "Detailed logs saved in: $LOGDIR/"
echo "=========================================="

# Create summary file
cat > "$LOGDIR/SUMMARY.txt" << EOF
CPU Component Simulation Summary
================================
Date: $(date)

Components Tested:
- RegisterFile: CPU register file (16-bit GPRs, dual-port read)
- JumpTest: Conditional jump evaluation logic
- ALU: Arithmetic/Logic Unit (ADD, SUB, AND, OR, XOR, shifts, rotates)

Test Results:
-------------
Total Test Cases: $total_tests
Passed:           $passed_tests
Failed:           $failed_tests

Overall Status: $(if [ $failed_tests -eq 0 ]; then echo "ALL TESTS PASSED"; else echo "SOME TESTS FAILED"; fi)

Individual Component Results:
EOF

for log in "$LOGDIR"/*.log; do
    if [ -f "$log" ]; then
        name=$(basename "$log" .log)
        tests=$(grep "Total Tests:" "$log" | awk '{print $3}')
        passed=$(grep "Passed:" "$log" | awk '{print $2}')
        failed=$(grep "Failed:" "$log" | awk '{print $2}')

        if [ -n "$tests" ]; then
            echo "" >> "$LOGDIR/SUMMARY.txt"
            echo "$name:" >> "$LOGDIR/SUMMARY.txt"
            echo "  Tests:  $tests" >> "$LOGDIR/SUMMARY.txt"
            echo "  Passed: $passed" >> "$LOGDIR/SUMMARY.txt"
            echo "  Failed: $failed" >> "$LOGDIR/SUMMARY.txt"
        fi
    fi
done

echo ""
echo "Summary written to: $LOGDIR/SUMMARY.txt"

# Exit with appropriate code
if [ $failed_tests -eq 0 ]; then
    exit 0
else
    exit 1
fi
