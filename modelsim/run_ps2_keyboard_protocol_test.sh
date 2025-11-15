#!/bin/bash

# Setup environment
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

# Create timestamp for results
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_DIR="sim_results_ps2_kbd_protocol_${TIMESTAMP}"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling PS2KeyboardController Protocol Testbench"
echo "================================================================"

# Compile with Icarus Verilog
iverilog -g2012 -Wall -DICARUS \
    -I../Quartus/rtl/ps2 \
    -I../Quartus/rtl/CPU \
    -I../Quartus/rtl/CPU/cdc \
    -o ps2_keyboard_protocol_sim \
    ../Quartus/rtl/ps2/PS2KeyboardController.sv \
    ../Quartus/rtl/ps2/PS2Host.sv \
    ../Quartus/rtl/ps2/KeyboardController.sv \
    ../Quartus/rtl/ps2/ScancodeTranslator.sv \
    ../Quartus/rtl/CPU/Fifo.sv \
    ../Quartus/rtl/CPU/cdc/BitSync.sv \
    ps2_keyboard_protocol_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! Check $RESULTS_DIR/compile.log"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running PS2KeyboardController Protocol Testbench"
echo "================================================================"
echo ""

# Run simulation
vvp ps2_keyboard_protocol_sim 2>&1 | tee "$RESULTS_DIR/simulation.log"

SIM_EXIT=$?

# Move VCD file to results directory
if [ -f "ps2_keyboard_protocol_tb.vcd" ]; then
    mv ps2_keyboard_protocol_tb.vcd "$RESULTS_DIR/"
    echo ""
    echo "VCD waveform saved to: $RESULTS_DIR/ps2_keyboard_protocol_tb.vcd"
fi

echo ""
echo "================================================================"
echo "Test Results Summary"
echo "================================================================"
echo "Output directory: $RESULTS_DIR"
echo ""

# Check results
if grep -q "ALL PS/2 PROTOCOL TESTS PASSED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo "✓✓✓ SUCCESS: All PS/2 protocol tests passed! ✓✓✓"
    exit 0
else
    echo ""
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
