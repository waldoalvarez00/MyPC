#!/bin/bash
# SegmentRegisterFile Unit Test

echo "========================================"
echo "SegmentRegisterFile Unit Test"
echo "========================================"

RTL_DIR="../Quartus/rtl"
CPU_DIR="$RTL_DIR/CPU"

mkdir -p sim_output

echo "Compiling..."
iverilog -g2012 \
    -o sim_output/segment_register_file_tb \
    -I$CPU_DIR \
    $CPU_DIR/SegmentRegisterFile.sv \
    $CPU_DIR/RegisterEnum.sv \
    segment_register_file_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Running simulation..."
cd sim_output
vvp segment_register_file_tb

exit $?
