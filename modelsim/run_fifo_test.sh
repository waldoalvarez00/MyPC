#!/bin/bash
# Fifo Unit Test

echo "========================================"
echo "Fifo Unit Test"
echo "========================================"

RTL_DIR="../Quartus/rtl"
CPU_DIR="$RTL_DIR/CPU"

mkdir -p sim_output

echo "Compiling..."
iverilog -g2012 \
    -o sim_output/fifo_tb \
    -I$CPU_DIR \
    $CPU_DIR/Fifo.sv \
    fifo_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Running simulation..."
cd sim_output
vvp fifo_tb

exit $?
