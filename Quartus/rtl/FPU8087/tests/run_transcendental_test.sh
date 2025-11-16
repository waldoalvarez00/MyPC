#!/bin/bash
# Compile and run transcendental function testbench

set -e  # Exit on error

echo "Compiling transcendental function testbench..."

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
TB="${ROOT_DIR}/tests/unit/tb_transcendental.v"

cd "${ROOT_DIR}"

# Compile with Icarus Verilog
iverilog -g2009 -Wall -o tb_transcendental.vvp \
    "${TB}" \
    FPU_Core.v \
    FPU_ArithmeticUnit.v \
    FPU_Transcendental.v \
    FPU_SQRT_Newton.v \
    FPU_CORDIC_Wrapper.v \
    FPU_Polynomial_Evaluator.v \
    FPU_Range_Reduction.v \
    FPU_Atan_Table.v \
    FPU_Poly_Coeff_ROM.v \
    CORDIC_Rotator.v \
    FPU_IEEE754_AddSub.v \
    FPU_IEEE754_Multiply.v \
    FPU_IEEE754_Divide.v \
    FPU_Int16_to_FP80.v \
    FPU_Int32_to_FP80.v \
    FPU_FP80_to_Int16.v \
    FPU_FP80_to_Int32.v \
    FPU_UInt64_to_FP80.v \
    FPU_FP80_to_UInt64.v \
    FPU_BCD_to_Binary.v \
    FPU_Binary_to_BCD.v \
    FPU_FP32_to_FP80.v \
    FPU_FP64_to_FP80.v \
    FPU_FP80_to_FP32.v \
    FPU_FP80_to_FP64.v \
    FPU_RegisterStack.v \
    FPU_StatusWord.v \
    FPU_ControlWord.v \
    FPU_IEEE754_MulDiv_Unified.v \
    FPU_Format_Converter_Unified.v \
    FPU_Payne_Hanek.v \
    FPU_Payne_Hanek_ROM.v \
    MicroSequencer_Extended_BCD.v \
    FPU_Exception_Handler.v \
    AddSubComp.v \
    LZCbit.v \
    LZCByte.v \
    ByteShifter.v \
    BitShifter.v \
    RoundUnit.v \
    Normalizer.v \
    BarrelShifter.v \
    MathConstants.v \
    2>&1 | tee compile.log

echo "Running simulation..."
vvp tb_transcendental.vvp | tee simulation.log
echo ""
echo "Simulation complete. Check simulation.log for results."
