#!/bin/bash
set -e

echo "============================================================"
echo "DCache2Way Flush/Write-back Test"
echo "============================================================"

TOP_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

iverilog -g2012 -o dcache2way_flush_tb \
    "$TOP_DIR/modelsim/dcache2way_flush_tb.sv" \
    "$TOP_DIR/Quartus/rtl/common/DCache2Way.sv" \
    "$TOP_DIR/Quartus/rtl/common/DPRam.sv" \
    "$TOP_DIR/Quartus/rtl/common/BlockRam.sv"

vvp dcache2way_flush_tb
