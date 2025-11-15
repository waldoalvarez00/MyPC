#!/bin/bash
# TempReg Unit Test

echo "========================================"
echo "TempReg Unit Test"
echo "========================================"

RTL_DIR="../Quartus/rtl"
CPU_DIR="$RTL_DIR/CPU"

mkdir -p sim_output

echo "Compiling..."
iverilog -g2012 \
    -o sim_output/temp_reg_tb \
    -I$CPU_DIR \
    $CPU_DIR/TempReg.sv \
    temp_reg_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Running simulation..."
cd sim_output
vvp temp_reg_tb

exit $?
