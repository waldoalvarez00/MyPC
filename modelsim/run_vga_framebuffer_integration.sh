#!/bin/bash
# VGA + FrameBuffer Integration Test Script
# Tests the complete VGA subsystem with FrameBuffer across multiple modes

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "========================================"
echo "VGA + FrameBuffer Integration Test"
echo "========================================"
echo ""

# Set up paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
VGA_DIR="$PROJECT_ROOT/Quartus/rtl/VGA"
CDC_DIR="$PROJECT_ROOT/Quartus/rtl/CPU/cdc"
TB_DIR="$SCRIPT_DIR"
OUTPUT_DIR="$SCRIPT_DIR/output"

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Change to testbench directory
cd "$TB_DIR"

echo "Compiling VGA + FrameBuffer integration testbench..."
echo ""

# Compile with Icarus Verilog
iverilog -g2012 \
    -DICARUS \
    -I"$VGA_DIR" \
    -I"$CDC_DIR" \
    -o "$OUTPUT_DIR/vga_framebuffer_integration_sim" \
    "$CDC_DIR/BitSync.sv" \
    "$CDC_DIR/SyncPulse.sv" \
    "$CDC_DIR/MCP.sv" \
    "$CDC_DIR/BusSync.sv" \
    "$VGA_DIR/VGATypes.sv" \
    "$VGA_DIR/VGASync.sv" \
    "$VGA_DIR/DACRam_sim.sv" \
    "$VGA_DIR/VGARegisters.sv" \
    "$VGA_DIR/VGAPrefetchRAM_sim.sv" \
    "$VGA_DIR/FBPrefetch.sv" \
    "$VGA_DIR/FrameBuffer.sv" \
    "$VGA_DIR/FontColorLUT.sv" \
    "$VGA_DIR/VGAController.sv" \
    "$TB_DIR/vga_framebuffer_integration_tb.sv"

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Compilation successful${NC}"
    echo ""
else
    echo -e "${RED}✗ Compilation failed${NC}"
    exit 1
fi

echo "Running VGA + FrameBuffer integration simulation..."
echo ""

# Run simulation
cd "$OUTPUT_DIR"
./vga_framebuffer_integration_sim

RESULT=$?

echo ""
if [ $RESULT -eq 0 ]; then
    echo -e "${GREEN}========================================"
    echo -e "✓ Integration Test Completed Successfully"
    echo -e "========================================${NC}"
else
    echo -e "${RED}========================================"
    echo -e "✗ Integration Test Failed"
    echo -e "========================================${NC}"
    exit 1
fi

# Check if VCD file was generated
if [ -f "vga_framebuffer_integration.vcd" ]; then
    echo ""
    echo "Waveform file generated: vga_framebuffer_integration.vcd"
    echo "View with: gtkwave vga_framebuffer_integration.vcd"
fi

echo ""
exit 0
