#!/bin/bash
# Flags Module Unit Test

echo "========================================"
echo "Flags Module Unit Test"
echo "========================================"

RTL_DIR="../Quartus/rtl"
CPU_DIR="$RTL_DIR/CPU"

mkdir -p sim_output

echo "Compiling..."
iverilog -g2012 \
    -o sim_output/flags_tb \
    -I$CPU_DIR \
    $CPU_DIR/Flags.sv \
    $CPU_DIR/FlagsEnum.sv \
    flags_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Running simulation..."
cd sim_output
vvp flags_tb

exit $?
