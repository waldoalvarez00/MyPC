#!/bin/bash

# Setup environment
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

# Create timestamp for results
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_DIR="sim_results_kfps2kb_${TIMESTAMP}"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling KFPS2KB Testbench (MiSTer Hardware - 30 MHz)"
echo "================================================================"

# Compile with Icarus Verilog
iverilog -g2012 -Wall -DICARUS \
    -I../Quartus/rtl/Keyboard \
    -I../Quartus/rtl/CPU/cdc \
    -o kfps2kb_sim \
    ../Quartus/rtl/Keyboard/KFPS2KB.sv \
    ../Quartus/rtl/Keyboard/KFPS2KB_Shift_Register.sv \
    kfps2kb_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! Check $RESULTS_DIR/compile.log"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running KFPS2KB Testbench"
echo "================================================================"
echo ""

# Run simulation
vvp kfps2kb_sim 2>&1 | tee "$RESULTS_DIR/simulation.log"

SIM_EXIT=$?

# Move VCD file to results directory
if [ -f "kfps2kb_tb.vcd" ]; then
    mv kfps2kb_tb.vcd "$RESULTS_DIR/"
    echo ""
    echo "VCD waveform saved to: $RESULTS_DIR/kfps2kb_tb.vcd"
fi

echo ""
echo "================================================================"
echo "Test Results Summary"
echo "================================================================"
echo "Output directory: $RESULTS_DIR"
echo ""

# Check results
if grep -q "ALL KFPS2KB TESTS PASSED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo "✓✓✓ SUCCESS: All KFPS2KB tests passed! ✓✓✓"
    exit 0
else
    echo ""
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
