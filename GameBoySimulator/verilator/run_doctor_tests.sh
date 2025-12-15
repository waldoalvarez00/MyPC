#!/bin/bash
# Run gameboy-doctor comparison for all Blargg CPU instruction tests

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Test ROM to reference log mapping
declare -A TESTS=(
    ["test_roms/cpu_instrs/individual/01-special.gb"]="1"
    ["test_roms/cpu_instrs/individual/02-interrupts.gb"]="2"
    ["test_roms/cpu_instrs/individual/03-op sp,hl.gb"]="3"
    ["test_roms/cpu_instrs/individual/04-op r,imm.gb"]="4"
    ["test_roms/cpu_instrs/individual/05-op rp.gb"]="5"
    ["test_roms/cpu_instrs/individual/06-ld r,r.gb"]="6"
    ["test_roms/cpu_instrs/individual/07-jr,jp,call,ret,rst.gb"]="7"
    ["test_roms/cpu_instrs/individual/08-misc instrs.gb"]="8"
    ["test_roms/cpu_instrs/individual/09-op r,r.gb"]="9"
    ["test_roms/cpu_instrs/individual/10-bit ops.gb"]="10"
    ["test_roms/cpu_instrs/individual/11-op a,(hl).gb"]="11"
)

mkdir -p logs

echo "=== GameBoy Doctor Test Suite ==="
echo ""

# Check if test binary exists
if [ ! -f "obj_dir/test_doctor_compare" ]; then
    echo "Error: obj_dir/test_doctor_compare not found"
    echo "Please compile with:"
    echo "  make -f Makefile.doctor test_doctor_compare"
    exit 1
fi

# Run each test
for rom in "${!TESTS[@]}"; do
    test_num="${TESTS[$rom]}"
    log_file="logs/test_${test_num}.log"

    echo "----------------------------------------"
    echo "Test $test_num: $(basename "$rom")"
    echo "----------------------------------------"

    # Run simulation and generate log
    ./obj_dir/test_doctor_compare "$rom" "$log_file" "reference_logs/${test_num}.log" 50000

    echo ""
done

echo "=== All Tests Complete ==="
echo ""
echo "To run gameboy-doctor comparison manually:"
echo "  python3 gameboy-doctor/gameboy-doctor logs/test_1.log cpu_instrs 1"
