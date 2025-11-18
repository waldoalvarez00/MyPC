#!/bin/bash
# Coherence test for ICache2Way <-> DCache2Way sideband

set -e

echo "================================================================"
echo "ICache2Way <-> DCache2Way Coherence Sideband Test"
echo "================================================================"
echo ""

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Clean previous artifacts
rm -f icache_dcache_coh_tb.vvp icache_dcache_coh_tb.vcd tb_icache_dcache_coh.log

echo "Compiling testbench..."
iverilog -g2012 -o icache_dcache_coh_tb.vvp \
    icache_dcache_coh_tb.sv \
    ../Quartus/rtl/common/ICache2Way.sv \
    ../Quartus/rtl/common/DCache2Way.sv \
    ../Quartus/rtl/common/DPRam.sv \
    ../Quartus/rtl/common/BlockRam.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful."
echo ""
echo "Running simulation..."
echo "================================================================"

vvp icache_dcache_coh_tb.vvp | tee tb_icache_dcache_coh.log
RESULT=$?

if [ $RESULT -ne 0 ]; then
    echo ""
    echo "================================================================"
    echo "✗ ICache/DCache coherence sideband test FAILED (rc=$RESULT)"
    echo "================================================================"
    echo "Artifacts kept:"
    echo "  - icache_dcache_coh_tb.vcd"
    echo "  - tb_icache_dcache_coh.log"
    exit 1
fi

rm -f icache_dcache_coh_tb.vvp

echo ""
echo "================================================================"
echo "✓ ICache/DCache coherence sideband test PASSED"
echo "================================================================"
echo ""
echo "Artifacts:"
echo "  - icache_dcache_coh_tb.vcd"
echo "  - tb_icache_dcache_coh.log"
echo ""

exit 0

