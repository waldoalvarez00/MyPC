#!/bin/bash

# Floppy Controller Testbench Simulation Script

echo "================================================"
echo "Compiling Floppy Controller Testbench"
echo "================================================"

# Get script directory to handle paths correctly
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

# Create output directory
RESULTS_DIR="sim_results_floppy_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULTS_DIR"

# Compile the design (stay in script dir)
iverilog -g2012 \
    -o "$RESULTS_DIR/floppy_tb" \
    -I../Quartus/rtl/Floppy \
    ../Quartus/rtl/Floppy/simplefifo.sv \
    ../Quartus/rtl/Floppy/floppy.sv \
    floppy_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

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
vvp "$RESULTS_DIR/floppy_tb" 2>&1 | tee "$RESULTS_DIR/simulation.log"

# Check simulation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Simulation failed! See simulation.log for details."
    exit 1
fi

# Move VCD if it was created
if [ -f "floppy_tb.vcd" ]; then
    mv floppy_tb.vcd "$RESULTS_DIR/"
fi

echo ""
echo "================================================"
echo "Simulation Complete"
echo "================================================"
echo ""
echo "Results saved to: $RESULTS_DIR"
echo ""
echo "Generated files:"
echo "  - compile.log     : Compilation messages"
echo "  - simulation.log  : Simulation output"
if [ -f "$RESULTS_DIR/floppy_tb.vcd" ]; then
    echo "  - floppy_tb.vcd   : Waveform data (view with GTKWave)"
fi
echo ""
echo "To view waveforms:"
echo "  gtkwave $RESULTS_DIR/floppy_tb.vcd"
echo ""

exit 0
