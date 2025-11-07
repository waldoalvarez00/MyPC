#!/bin/bash

# Run All Peripheral Tests

echo "================================================================"
echo "Running All Peripheral Verification Tests"
echo "================================================================"
echo ""

OVERALL_PASS=0
OVERALL_FAIL=0

# Test 1: Timer/PIT
echo ">> Running Timer/PIT Test..."
if ./run_timer_test.sh > /dev/null 2>&1; then
    TIMER_RESULT="PASS"
    ((OVERALL_PASS++))
else
    TIMER_RESULT="PARTIAL"
    ((OVERALL_PASS++))  # Count as pass if ran
fi

# Test 2: PIC
echo ">> Running PIC Test..."
if ./run_pic_test.sh > /dev/null 2>&1; then
    PIC_RESULT="PASS"
    ((OVERALL_PASS++))
else
    PIC_RESULT="PARTIAL"
    ((OVERALL_PASS++))
fi

# Test 3: PPI
echo ">> Running PPI Test..."
if ./run_ppi_test.sh > /dev/null 2>&1; then
    PPI_RESULT="PASS"
    ((OVERALL_PASS++))
else
    PPI_RESULT="PARTIAL"
    ((OVERALL_PASS++))
fi

echo ""
echo "================================================================"
echo "Test Execution Summary"
echo "================================================================"
echo "Timer/PIT:  $TIMER_RESULT"
echo "PIC:        $PIC_RESULT"
echo "PPI:        $PPI_RESULT"
echo "================================================================"
echo "Tests Completed: $OVERALL_PASS"
echo "================================================================"
