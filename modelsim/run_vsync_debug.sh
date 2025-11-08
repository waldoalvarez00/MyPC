#!/bin/bash

echo "========================================"
echo "Running CGA VSYNC Debug Test"
echo "========================================"

# Compile
iverilog -g2012 -DICARUS \
    -o cga_vsync_debug \
    -I../Quartus/rtl/CGA \
    ../Quartus/rtl/CGA/*.sv \
    cga_vsync_debug_tb.sv

if [ $? -ne 0 ]; then
    echo "Compilation failed!"
    exit 1
fi

# Run
./cga_vsync_debug

echo ""
echo "========================================"
echo "Test complete"
echo "========================================"
