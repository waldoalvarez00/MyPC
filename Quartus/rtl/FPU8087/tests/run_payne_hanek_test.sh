#!/bin/bash
# Run Payne-Hanek Range Reduction testbench

# Add Icarus Verilog to PATH if not already there
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

echo "========================================"
echo "Compiling and Running Payne-Hanek Test"
echo "========================================"

cd "$(dirname "$0")"

# Compile
iverilog -g2012 \
    -o payne_hanek_sim \
    ../FPU_Payne_Hanek.v \
    tb_payne_hanek.v

if [ $? -ne 0 ]; then
    echo "ERROR: Compilation failed!"
    exit 1
fi

# Run simulation
vvp payne_hanek_sim

# Cleanup
rm -f payne_hanek_sim

echo ""
echo "========================================"
echo "Payne-Hanek Simulation Complete"
echo "========================================"
