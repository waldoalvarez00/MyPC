#!/bin/bash
# LoopCounter Unit Test

echo "========================================"
echo "LoopCounter Unit Test"
echo "========================================"

RTL_DIR="../Quartus/rtl"
CPU_DIR="$RTL_DIR/CPU"

mkdir -p sim_output

echo "Compiling..."
iverilog -g2012 \
    -o sim_output/loop_counter_tb \
    -I$CPU_DIR \
    $CPU_DIR/LoopCounter.sv \
    loop_counter_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Running simulation..."
cd sim_output
vvp loop_counter_tb

exit $?
