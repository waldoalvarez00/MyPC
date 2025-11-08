#!/bin/bash
# Run JumpTest testbench

echo "========================================"
echo "Compiling and Running JumpTest Testbench"
echo "========================================"

cd "$(dirname "$0")"

# Compile
iverilog -g2012 \
    -I../Quartus/rtl/CPU \
    -o JumpTest_sim \
    ../Quartus/rtl/CPU/FlagsEnum.sv \
    ../Quartus/rtl/CPU/JumpTest.sv \
    JumpTest_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

# Run simulation
vvp JumpTest_sim

# Cleanup
rm -f JumpTest_sim

echo ""
echo "========================================"
echo "JumpTest Simulation Complete"
echo "========================================"
