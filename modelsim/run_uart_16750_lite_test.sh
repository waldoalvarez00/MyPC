#!/bin/bash

# UART 16750 Lite Test Script (SystemVerilog Translation Verification)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

RESULTS_DIR="sim_results_uart16750_lite_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling UART 16750 Lite (SystemVerilog Translation)"
echo "================================================================"
echo ""

# Compile all translated modules
iverilog -g2012 \
    -o "$RESULTS_DIR/uart16750_lite_tb" \
    -s uart_16750_lite_tb \
    ../Quartus/rtl/uart16750_sv/slib_edge_detect.sv \
    ../Quartus/rtl/uart16750_sv/slib_input_sync.sv \
    ../Quartus/rtl/uart16750_sv/slib_input_filter.sv \
    ../Quartus/rtl/uart16750_sv/slib_clock_div.sv \
    ../Quartus/rtl/uart16750_sv/slib_fifo.sv \
    ../Quartus/rtl/uart16750_sv/uart_baudgen.sv \
    ../Quartus/rtl/uart16750_sv/uart_transmitter.sv \
    ../Quartus/rtl/uart16750_sv/uart_16750_lite.sv \
    uart_16750_lite_tb.sv \
    > "$RESULTS_DIR/compile.log" 2>&1

if [ $? -ne 0 ]; then
    echo "[ERROR] Compilation failed! See compile.log for details."
    cat "$RESULTS_DIR/compile.log"
    exit 1
fi

echo "✓ Compilation successful"
echo ""
echo "================================================================"
echo "Running UART 16750 Lite Simulation"
echo "================================================================"
echo ""

# Run simulation
cd "$RESULTS_DIR"
vvp uart16750_lite_tb > simulation.log 2>&1
SIM_RESULT=$?

# Display results
cat simulation.log

echo ""
echo "================================================================"
echo "Simulation Complete"
echo "================================================================"
echo ""
echo "Results saved to: $RESULTS_DIR"
echo ""
echo "Generated files:"
echo "  - compile.log      : Compilation messages"
echo "  - simulation.log   : Simulation output and test results"
echo ""

# Check for success
if grep -q "SUCCESS: All UART translation tests passed" simulation.log; then
    echo "✓✓✓ SUCCESS: UART 16750 SystemVerilog translation verified! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
