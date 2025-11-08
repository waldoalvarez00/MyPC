#!/bin/bash
# Run RegisterFile testbench

echo "========================================"
echo "Compiling and Running RegisterFile Testbench"
echo "========================================"

cd "$(dirname "$0")"

# Compile
iverilog -g2012 \
    -I../Quartus/rtl/CPU \
    -o RegisterFile_sim \
    ../Quartus/rtl/CPU/RegisterEnum.sv \
    ../Quartus/rtl/CPU/RegisterFile.sv \
    RegisterFile_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

# Run simulation
vvp RegisterFile_sim

# Cleanup
rm -f RegisterFile_sim

echo ""
echo "========================================"
echo "RegisterFile Simulation Complete"
echo "========================================"
