#!/bin/bash
#
# Verilator compilation script for GameBoy simulator
# Now with full SDRAM and MBC support
#
# Usage: ./verilate_gameboy.sh
#

set -e

echo "=========================================="
echo "GameBoy Verilator Build Script"
echo "  - TV80 CPU (Verilog)"
echo "  - Full SDRAM support"
echo "  - MBC cartridge mappers"
echo "  - Sound APU (converted from VHDL)"
echo "=========================================="

# Change to script directory
cd "$(dirname "$0")"

# Paths
GAMEBOY_RTL="../gameboy_core/rtl"
TV80_RTL="../tv80/rtl/core"
STUB_RTL="../rtl"

echo "Compiling with Verilator..."

verilator \
    -Wall \
    --cc \
    --exe \
    --top-module top \
    -Wno-WIDTHEXPAND \
    -Wno-WIDTHTRUNC \
    -Wno-UNUSED \
    -Wno-UNOPTFLAT \
    -Wno-PINMISSING \
    -Wno-CASEINCOMPLETE \
    -Wno-TIMESCALEMOD \
    -Wno-DECLFILENAME \
    -Wno-MULTIDRIVEN \
    -Wno-BLKSEQ \
    -Wno-EOFNEWLINE \
    -Wno-PINCONNECTEMPTY \
    -Wno-GENUNNAMED \
    -Wno-VARHIDDEN \
    -Wno-ASCRANGE \
    -Wno-UNDRIVEN \
    -Wno-SYNCASYNCNET \
    -Wno-SELRANGE \
    --trace \
    -DGAMEBOY_SIM \
    \
    -I${GAMEBOY_RTL} \
    -I${GAMEBOY_RTL}/mappers \
    -I${TV80_RTL} \
    -I${STUB_RTL} \
    \
    gameboy_sim.v \
    \
    ${STUB_RTL}/tv80_gameboy.v \
    ${STUB_RTL}/gbc_snd_converted.v \
    ${STUB_RTL}/dpram.v \
    ${STUB_RTL}/spram.v \
    ${STUB_RTL}/bus_savestates.v \
    ${STUB_RTL}/gb_savestates.v \
    ${STUB_RTL}/gb_statemanager.v \
    ${STUB_RTL}/altddio_out.v \
    \
    ${TV80_RTL}/tv80_core.v \
    ${TV80_RTL}/tv80_alu.v \
    ${TV80_RTL}/tv80_reg.v \
    ${TV80_RTL}/tv80_mcode.v \
    \
    ${GAMEBOY_RTL}/gb.v \
    ${STUB_RTL}/video_sim.v \
    ${GAMEBOY_RTL}/cart.v \
    ${GAMEBOY_RTL}/timer.v \
    ${GAMEBOY_RTL}/hdma.v \
    ${GAMEBOY_RTL}/lcd.v \
    ${GAMEBOY_RTL}/sprites.v \
    ${GAMEBOY_RTL}/sprites_extra.v \
    ${GAMEBOY_RTL}/sprites_extra_store.v \
    ${GAMEBOY_RTL}/link.v \
    ${GAMEBOY_RTL}/sgb.v \
    ${STUB_RTL}/sdram_sim.sv \
    ${STUB_RTL}/cheatcodes_sim.sv \
    ${STUB_RTL}/megaswizzle_sim.sv \
    ${GAMEBOY_RTL}/savestate_ui.sv \
    ${GAMEBOY_RTL}/mappers/mappers.v \
    ${GAMEBOY_RTL}/mappers/mbc1.v \
    ${GAMEBOY_RTL}/mappers/mbc2.v \
    ${GAMEBOY_RTL}/mappers/mbc3.v \
    ${GAMEBOY_RTL}/mappers/mbc5.v \
    ${GAMEBOY_RTL}/mappers/mbc6.v \
    ${GAMEBOY_RTL}/mappers/mbc7.v \
    ${GAMEBOY_RTL}/mappers/mmm01.v \
    ${GAMEBOY_RTL}/mappers/huc1.v \
    ${GAMEBOY_RTL}/mappers/huc3.v \
    ${GAMEBOY_RTL}/mappers/tama.v \
    ${GAMEBOY_RTL}/mappers/gb_camera.v \
    ${GAMEBOY_RTL}/mappers/megaduck.v \
    ${GAMEBOY_RTL}/mappers/misc.v \
    ${GAMEBOY_RTL}/mappers/sachen.v \
    ${STUB_RTL}/rocket_sim.v \
    \
    sim_main.cpp

echo ""
echo "Verilator compilation complete!"
echo ""
echo "Now building C++ simulation..."

cd obj_dir
make -j$(nproc) -f Vtop.mk Vtop

echo ""
echo "=========================================="
echo "Build complete!"
echo ""
echo "Usage:"
echo "  ./obj_dir/Vtop [rom_file.gb]"
echo ""
echo "If no ROM file specified, loads ./game.gb"
echo "=========================================="
