#!/bin/bash
# Harvard Cache System Test Script
# Runs comprehensive testbench with Icarus Verilog

echo "========================================"
echo "Harvard Cache System Test"
echo "========================================"

# Set paths
RTL_DIR="../Quartus/rtl"
COMMON_DIR="$RTL_DIR/common"
CPU_DIR="$RTL_DIR/CPU"
TB_DIR="."

# Create output directory
mkdir -p sim_output

# Compile with Icarus Verilog
echo "Compiling RTL and testbench..."

iverilog -g2012 \
    -o sim_output/harvard_cache_tb \
    -I$COMMON_DIR \
    -I$CPU_DIR \
    $COMMON_DIR/BlockRam.sv \
    $COMMON_DIR/DPRam.sv \
    $COMMON_DIR/ICache.sv \
    $COMMON_DIR/DCache.sv \
    $COMMON_DIR/HarvardArbiter.sv \
    $COMMON_DIR/HarvardCacheSystem.sv \
    $TB_DIR/harvard_cache_tb.sv

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

echo "Compilation successful!"
echo ""

# Run simulation
echo "Running simulation..."
cd sim_output
vvp harvard_cache_tb

SIM_RESULT=$?

# Check results
echo ""
if [ $SIM_RESULT -eq 0 ]; then
    echo "========================================"
    echo "SIMULATION PASSED!"
    echo "========================================"
else
    echo "========================================"
    echo "SIMULATION FAILED!"
    echo "========================================"
fi

# Display waveform info
if [ -f harvard_cache_tb.vcd ]; then
    echo ""
    echo "Waveform file generated: sim_output/harvard_cache_tb.vcd"
    echo "View with: gtkwave sim_output/harvard_cache_tb.vcd"
fi

cd ..
exit $SIM_RESULT
