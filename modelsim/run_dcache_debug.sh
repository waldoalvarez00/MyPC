#!/bin/bash
# Debug test script for D-Cache Sequential Operations

echo "================================================================"
echo "D-Cache Sequential Operation Debug Test"
echo "================================================================"
echo ""
echo "This test focuses on the CPU Write → FPU Read scenario"
echo "with extensive debug traces to identify the issue."
echo ""
echo "================================================================"
echo ""

# Clean up
rm -f tb_dcache_coherency_debug.vvp tb_dcache_coherency_debug.vcd

# Compile
echo "Compiling debug testbench..."
iverilog -g2012 -o tb_dcache_coherency_debug.vvp \
    tb_dcache_coherency_debug.sv \
    ../Quartus/rtl/common/DCacheFrontendArbiter.sv \
    ../Quartus/rtl/common/DCache2Way.sv \
    ../Quartus/rtl/common/DPRam.sv \
    ../Quartus/rtl/common/BlockRam.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run simulation
echo "Running debug simulation..."
echo "================================================================"
vvp tb_dcache_coherency_debug.vvp

RESULT=$?

# Clean up
rm -f tb_dcache_coherency_debug.vvp tb_dcache_coherency_debug.vcd

exit $RESULT
