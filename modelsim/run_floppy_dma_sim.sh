#!/bin/bash

# Floppy DMA Transfer Testbench Simulation Script

echo "================================================================"
echo "Compiling Floppy DMA Transfer Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_floppy_dma_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling DMA controller and floppy controller modules..."
echo ""

# Compile the design
iverilog -g2012 -DICARUS \
    -o floppy_dma_tb \
    -I../../Quartus/rtl \
    -I../../Quartus/rtl/Floppy \
    -I../../Quartus/rtl/KF8237-DMA \
    ../../Quartus/rtl/Floppy/simplefifo.sv \
    ../../Quartus/rtl/Floppy/floppy.sv \
    ../../Quartus/rtl/KF8237-DMA/KF8237_Bus_Control_Logic.sv \
    ../../Quartus/rtl/KF8237-DMA/KF8237_Priority_Encoder.sv \
    ../../Quartus/rtl/KF8237-DMA/KF8237_Timing_And_Control.sv \
    ../../Quartus/rtl/KF8237-DMA/KF8237_Address_And_Count_Registers.sv \
    ../../Quartus/rtl/KF8237-DMA/KF8237.sv \
    ../../Quartus/rtl/KF8237-DMA/DMAUnit.sv \
    ../../modelsim/floppy_dma_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    echo "Common issues:"
    echo "  - Missing DMA controller source files"
    echo "  - Syntax errors in testbench"
    echo "  - Missing include paths"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running Floppy DMA Transfer Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp floppy_dma_tb 2>&1 | tee simulation.log

# Check simulation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Simulation failed! See simulation.log for details."
    exit 1
fi

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
echo "  - floppy_dma_tb.vcd  : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave floppy_dma_tb.vcd"
echo ""

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 5 simulation.log | tail -6
echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED" simulation.log; then
    echo "✓✓✓ SUCCESS: All DMA integration tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
