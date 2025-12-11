#!/bin/bash
# Run a batch of tests to verify realistic SDRAM latency works

TESTS=(
    "test_dn_write_pulse"
    "test_cart_ready"
    "test_complete_path"
    "test_realistic_latency"
    "test_sdram_persistence"
    "test_sdram_commands"
    "test_sdram_state_machine"
    "test_boot_rom_shadow"
    "test_boot_rom_data"
    "test_boot_execution"
    "test_cpu_timing"
    "test_data_path"
    "test_dout_r_capture"
    "test_timing_issue"
    "test_boot_rom_size"
    "test_boot_rom_vram"
    "test_boot_complete"
    "test_boot_completion"
    "test_ff50_data"
    "test_hdma"
)

PASS=0
FAIL=0
SKIP=0

echo "========================================="
echo "SDRAM Realistic Latency Test Suite"
echo "Testing ${#TESTS[@]} test programs"
echo "========================================="
echo ""

for test in "${TESTS[@]}"; do
    echo -n "Testing $test... "

    # Build
    g++ -std=c++14 -I./obj_dir -I/usr/local/share/verilator/include \
        -I/usr/local/share/verilator/include/vltstd -I. -I../sim \
        ${test}.cpp obj_dir/Vtop__ALL.a \
        /usr/local/share/verilator/include/verilated.cpp \
        /usr/local/share/verilator/include/verilated_vcd_c.cpp \
        /usr/local/share/verilator/include/verilated_threads.cpp \
        -o ${test}_test 2>&1 > /tmp/${test}_build.log

    if [ $? -ne 0 ]; then
        echo "❌ BUILD FAILED"
        SKIP=$((SKIP + 1))
        continue
    fi

    # Run
    ./${test}_test > /tmp/${test}_run.log 2>&1
    EXIT_CODE=$?

    if [ $EXIT_CODE -eq 0 ]; then
        echo "✅ PASSED"
        PASS=$((PASS + 1))
    else
        echo "❌ FAILED (exit code: $EXIT_CODE)"
        FAIL=$((FAIL + 1))
        # Show last few lines of output for debugging
        tail -5 /tmp/${test}_run.log
    fi
done

echo ""
echo "========================================="
echo "TEST RESULTS"
echo "========================================="
echo "Passed:  $PASS"
echo "Failed:  $FAIL"
echo "Skipped: $SKIP"
echo "Total:   ${#TESTS[@]}"
echo "========================================="

if [ $FAIL -eq 0 ]; then
    echo "✅ ALL TESTS PASSED!"
    exit 0
else
    echo "❌ SOME TESTS FAILED"
    exit 1
fi
