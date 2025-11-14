#!/bin/bash

#=============================================================================
# Test Script: Payne-Hanek Microcode Execution Test
#
# Compiles and runs the microcode testbench using Icarus Verilog
#=============================================================================

# Ensure iverilog is in PATH
if ! command -v iverilog &> /dev/null; then
    echo "iverilog not found in PATH, checking /tmp/iverilog_extract..."
    if [ -d "/tmp/iverilog_extract/usr/bin" ]; then
        export PATH="/tmp/iverilog_extract/usr/bin:$PATH"
        echo "Added iverilog to PATH"
    else
        echo "ERROR: iverilog not found. Please install it."
        exit 1
    fi
fi

# Set working directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FPU_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "========================================================================"
echo "  Payne-Hanek Microcode Test"
echo "========================================================================"
echo ""
echo "FPU Directory: $FPU_DIR"
echo ""

# Clean previous build
rm -f payne_hanek_microcode_test payne_hanek_microcode_test.vcd

# Compile testbench
echo "Compiling testbench..."
iverilog -g2009 \
    -o payne_hanek_microcode_test \
    -I"$FPU_DIR" \
    "$FPU_DIR/MicroSequencer_Extended_BCD.v" \
    "$FPU_DIR/FPU_Payne_Hanek_ROM.v" \
    "$SCRIPT_DIR/tb_payne_hanek_microcode.v" \
    2>&1 | tee compile.log

if [ $? -ne 0 ]; then
    echo ""
    echo "ERROR: Compilation failed!"
    echo "Check compile.log for details"
    exit 1
fi

echo ""
echo "Compilation successful!"
echo ""

# Run test
echo "Running test..."
echo "========================================================================"
echo ""

if [ -x "payne_hanek_microcode_test" ]; then
    ./payne_hanek_microcode_test | tee test_output.log
else
    vvp payne_hanek_microcode_test | tee test_output.log
fi

TEST_EXIT=$?

echo ""
echo "========================================================================"
echo ""

if [ $TEST_EXIT -eq 0 ]; then
    echo "Test completed!"
    echo ""
    echo "Output saved to: test_output.log"
    if [ -f "payne_hanek_microcode_test.vcd" ]; then
        echo "Waveform saved to: payne_hanek_microcode_test.vcd"
        echo "View with: gtkwave payne_hanek_microcode_test.vcd"
    fi
    echo ""
    echo "Review test_output.log for PASS/FAIL results"
else
    echo "Test failed with exit code $TEST_EXIT"
    exit $TEST_EXIT
fi

echo ""
echo "========================================================================"
