#!/bin/bash
# Arbiter Timing Debug Test

echo "========================================"
echo "Harvard Arbiter Timing Debug"
echo "========================================"

RTL_DIR="../Quartus/rtl"
COMMON_DIR="$RTL_DIR/common"

mkdir -p sim_output

echo "Compiling..."
iverilog -g2012 \
    -o sim_output/arbiter_timing_debug \
    -I$COMMON_DIR \
    $COMMON_DIR/HarvardArbiter.sv \
    arbiter_timing_debug.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Running simulation..."
cd sim_output
vvp arbiter_timing_debug

exit $?
