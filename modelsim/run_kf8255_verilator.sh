#!/bin/bash

echo "================================================================"
echo "Compiling KF8255 with Verilator"
echo "================================================================"

# Setup environment
export PATH="/tmp/verilator_extract/usr/bin:/tmp/make_extract/usr/bin:$PATH"
export VERILATOR_ROOT="/tmp/verilator_extract/usr/share/verilator"

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Cleaning previous build..."
rm -rf obj_dir

echo "Running Verilator..."
verilator --cc --exe --build -Wall \
    -I../Quartus/rtl/KF8255 \
    -I../Quartus/rtl \
    --top-module KF8255 \
    ../Quartus/rtl/KF8255/KF8255.sv \
    ../Quartus/rtl/KF8255/KF8255_Control_Logic.sv \
    ../Quartus/rtl/KF8255/KF8255_Group.sv \
    ../Quartus/rtl/KF8255/KF8255_Port.sv \
    ../Quartus/rtl/KF8255/KF8255_Port_C.sv \
    kf8255_tb.cpp

if [ $? -ne 0 ]; then
    echo ""
    echo "[ERROR] Verilator compilation failed!"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running KF8255 Testbench"
echo "================================================================"
echo ""

./obj_dir/VKF8255

EXIT_CODE=$?

echo ""
if [ $EXIT_CODE -eq 0 ]; then
    echo "✓✓✓ SUCCESS: All KF8255 Verilator tests passed! ✓✓✓"
else
    echo "⚠ WARNING: Some tests failed. Check output above."
fi

exit $EXIT_CODE
