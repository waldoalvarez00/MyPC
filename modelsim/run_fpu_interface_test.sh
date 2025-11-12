#!/bin/bash
# Test script for CPU-FPU interface integration

echo "==========================================="
echo "CPU-FPU Interface Integration Test"
echo "==========================================="

# Clean previous build
rm -f tb_fpu_interface tb_fpu_interface.vcd

# Compile CPU RTL files
echo "Compiling CPU RTL files..."
iverilog -g2012 -o tb_fpu_interface \
    -I../Quartus/rtl/CPU \
    -I../Quartus/rtl/common \
    tb_fpu_interface.sv \
    ../Quartus/rtl/CPU/RegisterEnum.sv \
    ../Quartus/rtl/CPU/FlagsEnum.sv \
    ../Quartus/rtl/CPU/Instruction.sv \
    ../Quartus/rtl/CPU/MicrocodeTypes.sv \
    ../Quartus/rtl/CPU/InstructionDefinitions.sv \
    ../Quartus/rtl/CPU/Core.sv \
    ../Quartus/rtl/CPU/Prefetch.sv \
    ../Quartus/rtl/CPU/RegisterFile.sv \
    ../Quartus/rtl/CPU/SegmentRegisterFile.sv \
    ../Quartus/rtl/CPU/Divider.sv \
    ../Quartus/rtl/CPU/LoadStore.sv \
    ../Quartus/rtl/CPU/IP.sv \
    ../Quartus/rtl/CPU/CSIPSync.sv \
    ../Quartus/rtl/CPU/Fifo.sv \
    ../Quartus/rtl/CPU/InsnDecoder.sv \
    ../Quartus/rtl/CPU/ModRMDecode.sv \
    ../Quartus/rtl/CPU/ImmediateReader.sv \
    ../Quartus/rtl/CPU/SegmentOverride.sv \
    ../Quartus/rtl/CPU/JumpTest.sv \
    ../Quartus/rtl/CPU/Flags.sv \
    ../Quartus/rtl/CPU/TempReg.sv \
    ../Quartus/rtl/CPU/LoopCounter.sv \
    ../Quartus/rtl/CPU/PosedgeToPulse.sv \
    ../Quartus/rtl/CPU/alu/ALU.sv

if [ $? -ne 0 ]; then
    echo "Compilation FAILED!"
    exit 1
fi

echo "Compilation successful!"
echo ""
echo "Running simulation..."
echo ""

# Run simulation
vvp tb_fpu_interface

# Check result
if [ $? -eq 0 ]; then
    echo ""
    echo "==========================================="
    echo "TEST PASSED"
    echo "==========================================="
    exit 0
else
    echo ""
    echo "==========================================="
    echo "TEST FAILED"
    echo "==========================================="
    exit 1
fi
