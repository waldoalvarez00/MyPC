#!/bin/bash

# Setup environment
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

# Create timestamp for results
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_DIR="sim_results_msmouse_wrapper_${TIMESTAMP}"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling MSMouseWrapper Testbench (MiSTer Hardware - 30 MHz)"
echo "================================================================"

# Compile with Icarus Verilog
iverilog -g2012 -Wall -DICARUS \
    -I../Quartus/rtl/MSMouse \
    -o msmouse_wrapper_sim \
    ../Quartus/rtl/MSMouse/MSMouseWrapper.v \
    msmouse_wrapper_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! Check $RESULTS_DIR/compile.log"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running MSMouseWrapper Testbench"
echo "================================================================"
echo ""

# Run simulation
vvp msmouse_wrapper_sim 2>&1 | tee "$RESULTS_DIR/simulation.log"

SIM_EXIT=$?

# Move VCD file to results directory
if [ -f "msmouse_wrapper_tb.vcd" ]; then
    mv msmouse_wrapper_tb.vcd "$RESULTS_DIR/"
    echo ""
    echo "VCD waveform saved to: $RESULTS_DIR/msmouse_wrapper_tb.vcd"
fi

echo ""
echo "================================================================"
echo "Test Results Summary"
echo "================================================================"
echo "Output directory: $RESULTS_DIR"
echo ""

# Check results
if grep -q "ALL MSMOUSEWRAPPER TESTS PASSED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo "✓✓✓ SUCCESS: All MSMouseWrapper tests passed! ✓✓✓"
    exit 0
else
    echo ""
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
