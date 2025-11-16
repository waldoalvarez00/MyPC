#!/bin/bash

echo "================================================================"
echo "Compiling KF8253 with Verilator"
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
    -I../Quartus/rtl/KF8253 \
    --top-module KF8253 \
    -Wno-WIDTHTRUNC \
    -Wno-WIDTHEXPAND \
    -Wno-CASEINCOMPLETE \
    -Wno-UNSIGNED \
    -Wno-UNOPTFLAT \
    -Wno-SELRANGE \
    ../Quartus/rtl/KF8253/KF8253.sv \
    ../Quartus/rtl/KF8253/KF8253_Counter.sv \
    ../Quartus/rtl/KF8253/KF8253_Control_Logic.sv \
    kf8253_tb.cpp

if [ $? -ne 0 ]; then
    echo ""
    echo "[ERROR] Verilator compilation failed!"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running KF8253 Testbench"
echo "================================================================"
echo ""

./obj_dir/VKF8253

exit_code=$?

echo ""
echo "================================================================"
echo "Test Complete"
echo "================================================================"

exit $exit_code
