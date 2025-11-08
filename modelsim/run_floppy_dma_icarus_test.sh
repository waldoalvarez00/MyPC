#!/bin/bash

# Floppy DMA Transfer Testbench Simulation Script (Icarus-Compatible)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

RESULT_DIR="sim_results_floppy_dma_icarus_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"

echo "================================================================"
echo "Compiling Floppy DMA Transfer Testbench (Icarus-Compatible)"
echo "================================================================"
echo ""
echo "Compiling DMA controller and floppy controller modules..."
echo ""

# Compile the design using Icarus-compatible DMA files
iverilog -g2012 \
    -o "$RESULT_DIR/floppy_dma_tb" \
    -I../Quartus/rtl \
    -I../Quartus/rtl/Floppy \
    -I../Quartus/rtl/KF8237-DMA-icarus \
    ../Quartus/rtl/Floppy/simplefifo.sv \
    ../Quartus/rtl/Floppy/floppy.sv \
    ../Quartus/rtl/KF8237-DMA-icarus/KF8237_Bus_Control_Logic.sv \
    ../Quartus/rtl/KF8237-DMA-icarus/KF8237_Priority_Encoder.sv \
    ../Quartus/rtl/KF8237-DMA-icarus/KF8237_Timing_And_Control.sv \
    ../Quartus/rtl/KF8237-DMA-icarus/KF8237_Address_And_Count_Registers.sv \
    ../Quartus/rtl/KF8237-DMA-icarus/KF8237.sv \
    ../Quartus/rtl/KF8237-DMA-icarus/DMAUnit.sv \
    floppy_dma_tb.sv \
    > "$RESULT_DIR/compile.log" 2>&1

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    cat "$RESULT_DIR/compile.log"
    exit 1
fi

echo "✓ Compilation successful"
echo ""
echo "================================================================"
echo "Running Floppy DMA Transfer Simulation"
echo "================================================================"
echo ""

# Run simulation
cd "$RESULT_DIR"
vvp floppy_dma_tb > simulation.log 2>&1
SIM_EXIT=$?

# Display results
cat simulation.log

echo ""
echo "================================================================"
echo "Simulation Complete"
echo "================================================================"
echo ""
echo "Results saved to: $RESULT_DIR"
echo ""
echo "Generated files:"
echo "  - compile.log        : Compilation messages"
echo "  - simulation.log     : Simulation output and test results"
echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED\|SUCCESS" simulation.log; then
    echo "✓✓✓ SUCCESS: All DMA integration tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ Note: DMA test run completed. Check simulation.log for details."
    exit $SIM_EXIT
fi
