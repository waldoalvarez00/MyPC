#!/bin/bash
# Test script for D-Cache Coherency (DCacheFrontendArbiter + DCache2Way)

echo "================================================================"
echo "D-Cache Coherency Test"
echo "================================================================"
echo ""
echo "This test validates that routing all data memory (CPU/DMA/FPU)"
echo "through the D-cache eliminates coherency violations."
echo ""
echo "Critical scenarios tested:"
echo "  1. DMA Write → CPU Read"
echo "  2. CPU Write → FPU Read"
echo "  3. FPU Write → CPU Read"
echo "  4. Mixed access patterns"
echo "  5. Byte-level coherency"
echo ""
echo "================================================================"
echo ""

# Clean up previous test artifacts
rm -f tb_dcache_coherency.vvp tb_dcache_coherency.vcd

# Compile the testbench
echo "Compiling testbench..."
iverilog -g2012 -o tb_dcache_coherency.vvp \
    tb_dcache_coherency.sv \
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

# Run the simulation
echo "Running simulation..."
echo "================================================================"
vvp tb_dcache_coherency.vvp

RESULT=$?

# Clean up
rm -f tb_dcache_coherency.vvp tb_dcache_coherency.vcd

if [ $RESULT -eq 0 ]; then
    echo ""
    echo "================================================================"
    echo "✓ D-Cache Coherency Test PASSED"
    echo "================================================================"
    echo ""
    echo "All data memory accesses (CPU/DMA/FPU) go through D-cache."
    echo "Cache coherency is guaranteed - no stale data violations."
    echo ""
    exit 0
else
    echo ""
    echo "================================================================"
    echo "✗ D-Cache Coherency Test FAILED"
    echo "================================================================"
    exit 1
fi
