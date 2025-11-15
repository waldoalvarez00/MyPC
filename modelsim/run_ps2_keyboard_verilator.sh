#!/bin/bash

echo "================================================================"
echo "Compiling PS2KeyboardController with Verilator"
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
    -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNUSEDSIGNAL -Wno-CASEINCOMPLETE \
    -I../Quartus/rtl/ps2 \
    -I../Quartus/rtl/CPU \
    -I../Quartus/rtl/CPU/cdc \
    -I../Quartus/rtl \
    --top-module PS2KeyboardController \
    ../Quartus/rtl/ps2/PS2KeyboardController.sv \
    ../Quartus/rtl/ps2/PS2Host.sv \
    ../Quartus/rtl/ps2/KeyboardController.sv \
    ../Quartus/rtl/ps2/ScancodeTranslator.sv \
    ../Quartus/rtl/CPU/Fifo.sv \
    ../Quartus/rtl/CPU/cdc/BitSync.sv \
    ps2_keyboard_tb.cpp

if [ $? -ne 0 ]; then
    echo ""
    echo "[ERROR] Verilator compilation failed!"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running PS2KeyboardController Testbench"
echo "================================================================"
echo ""

./obj_dir/VPS2KeyboardController

EXIT_CODE=$?

echo ""
if [ $EXIT_CODE -eq 0 ]; then
    echo "✓✓✓ SUCCESS: All PS2KeyboardController Verilator tests passed! ✓✓✓"
else
    echo "⚠ WARNING: Some tests failed. Check output above."
fi

exit $EXIT_CODE
