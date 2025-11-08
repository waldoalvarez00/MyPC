#!/bin/bash

# PIC (8259) Testbench Simulation Script

echo "================================================================"
echo "Compiling PIC (8259) Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_pic_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling PIC module and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o pic_tb \
    -I../../Quartus/rtl \
    -I../../Quartus/rtl/KF8259 \
    ../../Quartus/rtl/KF8259/KF8259.sv \
    ../../Quartus/rtl/KF8259/KF8259_Bus_Control_Logic.sv \
    ../../Quartus/rtl/KF8259/KF8259_Control_Logic.sv \
    ../../Quartus/rtl/KF8259/KF8259_Interrupt_Request.sv \
    ../../Quartus/rtl/KF8259/KF8259_Priority_Resolver.sv \
    ../../Quartus/rtl/KF8259/KF8259_In_Service.sv \
    ../../modelsim/pic_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running PIC (8259) Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp pic_tb 2>&1 | tee simulation.log

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
echo "  - compile.log      : Compilation messages"
echo "  - simulation.log   : Simulation output and test results"
echo "  - pic_tb.vcd       : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave pic_tb.vcd"
echo ""

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 5 simulation.log | tail -6
echo ""

# Check if all tests passed
if grep -q "ALL TESTS PASSED" simulation.log; then
    echo "✓✓✓ SUCCESS: All PIC tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
