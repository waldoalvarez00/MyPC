#!/bin/bash

# Floppy Controller Testbench Simulation Script

echo "================================================"
echo "Compiling Floppy Controller Testbench"
echo "================================================"

# Create output directory
mkdir -p sim_results_floppy_$(date +%Y%m%d_%H%M%S)
cd sim_results_floppy_$(date +%Y%m%d_%H%M%S)

# Compile the design
iverilog -g2012 \
    -o floppy_tb \
    -I../Quartus/rtl/Floppy \
    ../Quartus/rtl/Floppy/simplefifo.sv \
    ../Quartus/rtl/Floppy/floppy.sv \
    ../modelsim/floppy_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================"
echo "Running Floppy Controller Simulation"
echo "================================================"
echo ""

# Run simulation
vvp floppy_tb 2>&1 | tee simulation.log

# Check simulation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Simulation failed! See simulation.log for details."
    exit 1
fi

echo ""
echo "================================================"
echo "Simulation Complete"
echo "================================================"
echo ""
echo "Results saved to: sim_results_floppy_$(basename $(pwd))"
echo ""
echo "Generated files:"
echo "  - compile.log     : Compilation messages"
echo "  - simulation.log  : Simulation output"
echo "  - floppy_tb.vcd   : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave floppy_tb.vcd"
echo ""

exit 0
