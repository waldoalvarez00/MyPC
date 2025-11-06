#!/bin/bash
# Script to run Verilator lint on the PCXT project
# Install Verilator first: sudo apt-get install verilator

cd "$(dirname "$0")"

echo "Running Verilator lint on PCXT design..."
echo "========================================"

# Run Verilator in lint-only mode
verilator --lint-only \
    -Wall \
    -Wno-fatal \
    -sv \
    --top-module emu \
    -I. \
    -Istubs \
    -Irtl \
    -Irtl/CPU \
    -Irtl/CGA \
    -Irtl/VGA \
    -Irtl/KF8237-DMA \
    -Irtl/KF8253 \
    -Irtl/KF8255 \
    -Irtl/KF8259 \
    -Irtl/Keyboard \
    -Irtl/Floppy \
    -Irtl/Debug \
    -Irtl/bios \
    -Irtl/common \
    -Irtl/irq \
    -Irtl/leds \
    -Irtl/pic \
    -Irtl/ps2 \
    -Irtl/sdram \
    -Irtl/timer \
    -Irtl/uart \
    --error-limit 100 \
    stubs/pll.v \
    stubs/pllsdram.v \
    stubs/hps_io.sv \
    mycore.sv \
    rtl/IDArbiter.sv \
    rtl/DMAArbiter.sv \
    rtl/MemArbiterExtend.sv \
    rtl/AddressDecoder.sv \
    rtl/AckExtender.sv \
    rtl/CPU/Core.sv \
    rtl/CPU/CSIPSync.sv \
    rtl/CPU/Divider.sv \
    rtl/CPU/Fifo.sv \
    rtl/CPU/Flags.sv \
    rtl/CPU/FlagsEnum.sv \
    rtl/CPU/IP.sv \
    rtl/CPU/ImmediateReader.sv \
    rtl/CPU/InsnDecoder.sv \
    rtl/CPU/Instruction.sv \
    rtl/CPU/InstructionDefinitions.sv \
    rtl/CPU/JumpTest.sv \
    rtl/CPU/LoadStore.sv \
    rtl/CPU/LoopCounter.sv \
    rtl/CPU/MemArbiter.sv \
    rtl/CPU/Microcode.sv \
    rtl/CPU/MicrocodeTypes.sv \
    rtl/CPU/ModRMDecode.sv \
    rtl/CPU/PosedgeToPulse.sv \
    rtl/CPU/Prefetch.sv \
    rtl/CPU/RegisterEnum.sv \
    rtl/CPU/RegisterFile.sv \
    rtl/CPU/SegmentOverride.sv \
    rtl/CPU/SegmentRegisterFile.sv \
    rtl/CPU/TempReg.sv \
    rtl/CPU/alu/*.sv \
    rtl/CPU/cdc/*.sv \
    rtl/CGA/*.sv \
    rtl/VGA/*.sv \
    rtl/VGA/DACRam.v \
    rtl/KF8237-DMA/*.sv \
    rtl/KF8253/*.sv \
    rtl/KF8255/*.sv \
    rtl/KF8259/*.sv \
    rtl/Keyboard/*.sv \
    rtl/MSMouse/MSMouseWrapper.v \
    rtl/Floppy/*.sv \
    rtl/Debug/*.sv \
    rtl/bios/*.sv \
    rtl/irq/*.sv \
    rtl/leds/*.sv \
    rtl/pic/*.sv \
    rtl/ps2/*.sv \
    rtl/sdram/*.sv \
    rtl/sdramtut6.sv \
    rtl/timer/*.sv \
    rtl/uart/*.sv \
    rtl/uart16750/uart.v \
    rtl/common/*.sv \
    2>&1 | tee verilator_lint.log

echo ""
echo "========================================"
echo "Verilator lint complete. See verilator_lint.log for details."
echo ""
echo "Summary:"
grep -E "(Error|Warning)" verilator_lint.log | wc -l | xargs -I {} echo "Total Errors/Warnings: {}"
