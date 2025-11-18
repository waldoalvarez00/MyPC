#!/bin/bash
set -e
echo "============================================================"
echo "Harvard Cache Random Coherence Test"
echo "============================================================"
TOP_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
iverilog -g2012 -o harvard_cache_random_tb \
    "$TOP_DIR/modelsim/harvard_cache_random_tb.sv" \
    "$TOP_DIR/Quartus/rtl/common/ICache2Way.sv" \
    "$TOP_DIR/Quartus/rtl/common/DCache2Way.sv" \
    "$TOP_DIR/Quartus/rtl/common/CacheArbiter.sv" \
    "$TOP_DIR/Quartus/rtl/common/DPRam.sv" \
    "$TOP_DIR/Quartus/rtl/common/BlockRam.sv"
vvp harvard_cache_random_tb
