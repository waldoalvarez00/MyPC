#!/bin/bash
# Run SDRAM Verilator Model Test
#
# Usage: ./run_sdram_test.sh [--trace]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "================================================"
echo "SDRAM Verilator Model Test"
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
rm -f sdram_test.vcd

# Build
echo "Building SDRAM test..."
make -f Makefile.sdram

if [ $? -ne 0 ]; then
    echo "ERROR: Build failed"
    exit 1
fi

echo ""
echo "Build successful!"
echo ""

# Run test
if [ "$1" == "--trace" ]; then
    echo "Running test with waveform tracing..."
    ./obj_dir/Vsdram_test_top --trace
    echo ""
    echo "Waveform saved to sdram_test.vcd"
    echo "View with: gtkwave sdram_test.vcd"
else
    echo "Running test..."
    ./obj_dir/Vsdram_test_top
fi

echo ""
echo "Test complete!"
