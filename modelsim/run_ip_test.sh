#!/bin/bash
# IP (Instruction Pointer) Unit Test

echo "========================================"
echo "IP Unit Test"
echo "========================================"

RTL_DIR="../Quartus/rtl"
CPU_DIR="$RTL_DIR/CPU"

mkdir -p sim_output

echo "Compiling..."
iverilog -g2012 \
    -o sim_output/ip_tb \
    -I$CPU_DIR \
    $CPU_DIR/IP.sv \
    ip_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Running simulation..."
cd sim_output
vvp ip_tb

exit $?
