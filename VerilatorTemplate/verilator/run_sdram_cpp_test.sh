#!/bin/bash
# Run C++ SDRAM Model Verilator Test
#
# Usage: ./run_sdram_cpp_test.sh [--trace] [--debug]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Set up Verilator path
export PATH="/tmp/verilator_install/usr/bin:$PATH"

echo "================================================"
echo "C++ SDRAM Model Verilator Test"
echo "================================================"
echo ""

# Check for Verilator
if ! command -v verilator &> /dev/null; then
    echo "ERROR: Verilator not found in PATH"
    echo "Please install Verilator or add it to your PATH"
    exit 1
fi

echo "Verilator version: $(verilator --version)"
echo ""

# Clean previous build
echo "Cleaning previous build..."
rm -rf obj_dir
rm -f sdram_cpp_test.vcd

# Build
echo "Building C++ SDRAM test..."
make -f Makefile.sdram_cpp

if [ $? -ne 0 ]; then
    echo "ERROR: Build failed"
    exit 1
fi

echo ""
echo "Build successful!"
echo ""

# Run test
ARGS=""
if [[ "$*" == *"--trace"* ]]; then
    ARGS="$ARGS --trace"
fi
if [[ "$*" == *"--debug"* ]]; then
    ARGS="$ARGS --debug"
fi

echo "Running test$ARGS..."
./obj_dir/Vsdram_ctrl_sim $ARGS

if [[ "$*" == *"--trace"* ]]; then
    echo ""
    echo "Waveform saved to sdram_cpp_test.vcd"
    echo "View with: gtkwave sdram_cpp_test.vcd"
fi

echo ""
echo "Test complete!"
