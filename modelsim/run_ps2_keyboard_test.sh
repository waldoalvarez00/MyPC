#!/bin/bash

# Create timestamp for results
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_DIR="sim_results_ps2_keyboard_${TIMESTAMP}"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling PS2KeyboardController Testbench"
echo "================================================================"
echo ""
echo "Compiling PS/2 Keyboard controller and testbench..."
echo ""

# Compile with Icarus Verilog
iverilog -g2012 -DICARUS \
    -o "$RESULTS_DIR/ps2_keyboard_tb" \
    -s ps2_keyboard_tb \
    ../Quartus/rtl/ps2/PS2KeyboardController.sv \
    ../Quartus/rtl/ps2/KeyboardController.sv \
    ../Quartus/rtl/ps2/ScancodeTranslator.sv \
    ../Quartus/rtl/ps2/PS2Host.sv \
    ../Quartus/rtl/CPU/Fifo.sv \
    ../Quartus/rtl/CPU/cdc/BitSync.sv \
    ps2_keyboard_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "❌ Compilation failed! Check compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running PS2KeyboardController Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp "$RESULTS_DIR/ps2_keyboard_tb" 2>&1 | tee "$RESULTS_DIR/simulation.log"

# Extract test results
echo ""
echo "================================================================"
echo "Simulation Complete"
echo "================================================================"
echo ""
echo "Results saved to: $RESULTS_DIR"
echo ""
echo "Generated files:"
echo "  - compile.log         : Compilation messages"
echo "  - simulation.log      : Simulation output and test results"
echo "  - ps2_keyboard_tb.vcd : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave ps2_keyboard_tb.vcd"
echo ""

# Show test summary
echo "Test Results Summary:"
echo "---------------------"
grep -A 5 "Test Summary" "$RESULTS_DIR/simulation.log"

# Check if all tests passed
if grep -q "ALL CPU INTERFACE TESTS PASSED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo "✓✓✓ SUCCESS: All PS2KeyboardController interface tests passed! ✓✓✓"
    exit 0
else
    echo ""
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
