#!/bin/bash

echo "================================================================"
echo "Compiling SpeakerAudioConverter with Icarus Verilog"
echo "================================================================"

# Setup environment
export PATH="/tmp/iverilog_extract/usr/bin:$PATH"

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Create output directory
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_DIR="sim_results_speaker_audio_${TIMESTAMP}"
mkdir -p "$OUTPUT_DIR"

echo "Compiling modules..."
iverilog -g2012 -Wall \
    -I../Quartus/rtl/audio \
    -o speaker_audio_converter_sim \
    ../Quartus/rtl/audio/SpeakerAudioConverter.sv \
    speaker_audio_converter_tb.sv

if [ $? -ne 0 ]; then
    echo ""
    echo "[ERROR] Compilation failed!"
    exit 1
fi

echo ""
echo "================================================================"
echo "Running SpeakerAudioConverter Testbench"
echo "================================================================"
echo ""

# Run simulation and capture output
vvp speaker_audio_converter_sim | tee "$OUTPUT_DIR/test_output.txt"

EXIT_CODE=${PIPESTATUS[0]}

# Move VCD file to output directory
if [ -f "speaker_audio_converter_tb.vcd" ]; then
    mv speaker_audio_converter_tb.vcd "$OUTPUT_DIR/"
fi

echo ""
echo "================================================================"
echo "Test Results"
echo "================================================================"
echo "Output directory: $OUTPUT_DIR"
echo "VCD file: $OUTPUT_DIR/speaker_audio_converter_tb.vcd"
echo ""

if [ $EXIT_CODE -eq 0 ]; then
    # Check if all tests passed
    if grep -q "ALL SPEAKER AUDIO CONVERTER TESTS PASSED" "$OUTPUT_DIR/test_output.txt"; then
        echo "✓✓✓ SUCCESS: All SpeakerAudioConverter tests passed! ✓✓✓"
        exit 0
    else
        echo "⚠ WARNING: Some tests failed. Check output above."
        exit 1
    fi
else
    echo "⚠ ERROR: Simulation failed with exit code $EXIT_CODE"
    exit $EXIT_CODE
fi
