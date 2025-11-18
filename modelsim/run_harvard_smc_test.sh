#!/bin/bash
# Harvard I/D Cache Self-Modifying Code Test

set -e

echo "============================================================"
echo "Harvard I/D Cache Self-Modifying Code Test"
echo "ICache2Way + DCache2Way + CacheArbiter + PipelinedMemArbiterExtend"
echo "============================================================"
echo ""

TOP_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RTL_COMMON="$TOP_DIR/Quartus/rtl/common"

rm -f harvard_smc_tb.vvp harvard_smc_tb.vcd || true

echo "[*] Compiling testbench with iverilog..."
iverilog -g2012 -o harvard_smc_tb.vvp \
    harvard_smc_tb.sv \
    "$RTL_COMMON/ICache2Way.sv" \
    "$RTL_COMMON/DCache2Way.sv" \
    "$RTL_COMMON/CacheArbiter.sv" \
    "$RTL_COMMON/DPRam.sv" \
    "$RTL_COMMON/BlockRam.sv" \
    "$TOP_DIR/Quartus/rtl/PipelinedMemArbiterExtend.sv"

echo ""
echo "[*] Running simulation..."
vvp harvard_smc_tb.vvp
STATUS=$?

rm -f harvard_smc_tb.vvp

if [ $STATUS -eq 0 ]; then
    echo ""
    echo "============================================================"
    echo "✓ Harvard self-modifying code test PASSED"
    echo "============================================================"
    exit 0
else
    echo ""
    echo "============================================================"
    echo "✗ Harvard self-modifying code test FAILED"
    echo "============================================================"
    exit 1
fi

