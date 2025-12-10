#!/bin/bash
# Build and run comprehensive CPU test

set -e  # Exit on error

echo "========================================" echo "Building GameBoy CPU Comprehensive Test"
echo "========================================"

# Clean previous build
rm -f test_cpu_comprehensive test_cpu_comprehensive.o

# Verilate if needed (reuse existing obj_dir if available)
if [ ! -d "obj_dir" ]; then
    echo "Running Verilator (this may take a minute)..."
    ./verilate_gameboy.sh
fi

echo ""
echo "Compiling test..."

# Compile the test
g++ -std=c++14 \
    -I./obj_dir \
    -I/usr/local/share/verilator/include \
    -I/usr/local/share/verilator/include/vltstd \
    -I.. \
    test_cpu_comprehensive.cpp \
    obj_dir/Vtop__ALL.a \
    /usr/local/share/verilator/include/verilated.cpp \
    /usr/local/share/verilator/include/verilated_vcd_c.cpp \
    /usr/local/share/verilator/include/verilated_threads.cpp \
    -o test_cpu_comprehensive

if [ $? -ne 0 ]; then
    echo "Compilation failed!"
    exit 1
fi

echo ""
echo "========================================"
echo "Running CPU Comprehensive Test"
echo "========================================"
echo ""

# Run the test
./test_cpu_comprehensive

TEST_RESULT=$?

echo ""
if [ $TEST_RESULT -eq 0 ]; then
    echo "✅ ALL TESTS PASSED"
else
    echo "❌ TESTS FAILED (exit code: $TEST_RESULT)"
fi

exit $TEST_RESULT
