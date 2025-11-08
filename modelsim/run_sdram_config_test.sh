#!/bin/bash

# SDRAM Config Register Test Script

echo "================================================================"
echo "Compiling SDRAM Config Register Testbench"
echo "================================================================"

# Create output directory
RESULT_DIR="sim_results_sdram_config_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$RESULT_DIR"
cd "$RESULT_DIR"

echo ""
echo "Compiling SDRAMConfigRegister and testbench..."
echo ""

# Compile the design
iverilog -g2012 \
    -o sdram_config_tb \
    -Dverilator \
    -I../../Quartus/rtl \
    -I../../Quartus/rtl/sdram \
    ../../Quartus/rtl/sdram/SDRAMConfigRegister.sv \
    ../../modelsim/sdram_config_tb.sv \
    2>&1 | tee compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed! See compile.log for details."
    exit 1
fi

echo ""
echo "================================================================"
echo "Running SDRAM Config Register Simulation"
echo "================================================================"
echo ""

# Run simulation
vvp sdram_config_tb 2>&1 | tee simulation.log

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

# Parse results
echo "Test Results Summary:"
echo "---------------------"
grep "Test Summary" -A 6 simulation.log | tail -7
echo ""

# Check if all tests passed
if grep -q "SUCCESS: All SDRAM Config Register tests passed" simulation.log; then
    echo "✓✓✓ SUCCESS: All SDRAM Config Register tests passed! ✓✓✓"
    exit 0
else
    echo "⚠ WARNING: Some tests may have failed. Check simulation.log for details."
    exit 1
fi
