#!/bin/bash

# Create timestamp for results
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_DIR="sim_results_mem_arbiter_extend_${TIMESTAMP}"
mkdir -p "$RESULTS_DIR"

echo "================================================================"
echo "Compiling MemArbiterExtend Testbench"
echo "================================================================"
echo ""
echo "Compiling MemArbiterExtend module and testbench..."
echo ""

# Compile with Icarus Verilog
iverilog -g2012 \
    -o "$RESULTS_DIR/mem_arbiter_extend_tb" \
    -s mem_arbiter_extend_tb \
    ../Quartus/rtl/MemArbiterExtend.sv \
    mem_arbiter_extend_tb.sv \
    2>&1 | tee "$RESULTS_DIR/compile.log"

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "❌ Compilation failed! Check compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running MemArbiterExtend Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp "$RESULTS_DIR/mem_arbiter_extend_tb" 2>&1 | tee "$RESULTS_DIR/simulation.log"

# Extract test results
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
echo "  - mem_arbiter_extend_tb.vcd : Waveform data (view with GTKWave)"
echo ""
echo "To view waveforms:"
echo "  gtkwave mem_arbiter_extend_tb.vcd"
echo ""

# Show test summary
echo "Test Results Summary:"
echo "---------------------"
grep -A 5 "Test Summary" "$RESULTS_DIR/simulation.log"

# Check if all tests passed
if grep -q "ALL TESTS PASSED" "$RESULTS_DIR/simulation.log"; then
    echo ""
    echo "✓✓✓ SUCCESS: All MemArbiterExtend tests passed! ✓✓✓"
    exit 0
else
    echo ""
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
