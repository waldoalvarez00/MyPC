#!/bin/bash
# Run ALU testbench

echo "========================================"
echo "Compiling and Running ALU Testbench"
echo "========================================"

cd "$(dirname "$0")"

# Compile - ALU requires all task files
iverilog -g2012 \
    -I../Quartus/rtl/CPU \
    -I../Quartus/rtl/CPU/alu \
    -o ALU_sim \
    ../Quartus/rtl/CPU/FlagsEnum.sv \
    ../Quartus/rtl/CPU/MicrocodeTypes.sv \
    ../Quartus/rtl/CPU/alu/flags.sv \
    ../Quartus/rtl/CPU/alu/add.sv \
    ../Quartus/rtl/CPU/alu/adc.sv \
    ../Quartus/rtl/CPU/alu/sub.sv \
    ../Quartus/rtl/CPU/alu/and.sv \
    ../Quartus/rtl/CPU/alu/or.sv \
    ../Quartus/rtl/CPU/alu/xor.sv \
    ../Quartus/rtl/CPU/alu/not.sv \
    ../Quartus/rtl/CPU/alu/shl.sv \
    ../Quartus/rtl/CPU/alu/shr.sv \
    ../Quartus/rtl/CPU/alu/sar.sv \
    ../Quartus/rtl/CPU/alu/rol.sv \
    ../Quartus/rtl/CPU/alu/ror.sv \
    ../Quartus/rtl/CPU/alu/rcl.sv \
    ../Quartus/rtl/CPU/alu/rcr.sv \
    ../Quartus/rtl/CPU/alu/mul.sv \
    ../Quartus/rtl/CPU/alu/extend.sv \
    ../Quartus/rtl/CPU/alu/bound.sv \
    ../Quartus/rtl/CPU/alu/aaa.sv \
    ../Quartus/rtl/CPU/alu/aas.sv \
    ../Quartus/rtl/CPU/alu/daa.sv \
    ../Quartus/rtl/CPU/alu/das.sv \
    ../Quartus/rtl/CPU/alu/enter.sv \
    ../Quartus/rtl/CPU/alu/shift_flags.sv \
    ../Quartus/rtl/CPU/alu/ALU.sv \
    ALU_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

# Run simulation
vvp ALU_sim

# Cleanup
rm -f ALU_sim

echo ""
echo "========================================"
echo "ALU Simulation Complete"
echo "========================================"
