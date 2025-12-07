# GameBoy Verilator Simulator

A Verilator-based simulation of the GameBoy MiSTer core with the TV80 Verilog CPU replacing the original VHDL T80 CPU.

## Overview

This simulator combines:
- **GameBoy MiSTer Core** - Full GameBoy/GameBoy Color emulation from [MiSTer-devel/Gameboy_MiSTer](https://github.com/MiSTer-devel/Gameboy_MiSTer)
- **TV80 Z80 CPU** - Verilog implementation from [hutch31/tv80](https://github.com/hutch31/tv80)
- **C++ SDRAM Model** - MisterSDRAMModel for accurate SDRAM timing simulation
- **Verilator Simulation Framework** - ImGui-based interactive GUI

## Key Features

1. **TV80 CPU** - Replaces T80 (VHDL) with TV80 (Verilog) using Game Boy mode (Mode=3)
2. **Full SDRAM Support** - Uses C++ MisterSDRAMModel for 32MB SDRAM emulation
3. **MBC Mapper Support** - All cartridge mappers (MBC1-5, HuC1/3, etc.) fully functional
4. **Large ROM Support** - ROMs up to 8MB supported via SDRAM
5. **Verilog Stubs** - For VHDL modules (dpram, gbc_snd, savestates)

## Directory Structure

```
GameBoySimulator/
├── gameboy_core/       # Cloned GameBoy MiSTer core
│   └── rtl/            # Original RTL files (including sdram.sv, cart.v)
├── tv80/               # Cloned TV80 Z80 Verilog core
│   └── rtl/core/       # TV80 core files
├── rtl/                # Custom stubs and wrappers
│   ├── tv80_gameboy.v  # TV80-based GBse replacement
│   ├── gbc_snd.v       # Sound module stub
│   ├── dpram.v         # Dual-port RAM
│   ├── spram.v         # Single-port RAM
│   ├── bus_savestates.v
│   ├── gb_savestates.v
│   └── gb_statemanager.v
├── sim/                # C++ simulation models
│   ├── mister_sdram_model.h  # SDRAM simulation model
│   └── sim_sdram.h           # SDRAM utilities
├── verilator/          # Simulation files
│   ├── gameboy_sim.v   # Top-level wrapper with SDRAM
│   ├── sim_main.cpp    # C++ simulation main
│   ├── verilate_gameboy.sh  # Build script
│   └── sim/            # ImGui and simulation support
```

## Environment setup

### Windows
- Install WSL2 with Ubuntu
- Install Visual Studio 2022 (Community edition is fine) with the C++ workload

### WSL (verilator)

This project is built and tested with Verilator v5.026. Keep your Verilator install in sync to avoid API/compile errors.
To install v5.026, run the following commands from a temporary directory:

```bash
# Prerequisites:
sudo apt-get install git perl python3 make autoconf g++ flex bison ccache
sudo apt-get install libgoogle-perftools-dev numactl perl-doc
sudo apt-get install zlibc zlib1g zlib1g-dev

git clone https://github.com/verilator/verilator

unset VERILATOR_ROOT
cd verilator
git pull
git checkout v5.026
autoconf
./configure
make -j `nproc`
sudo make install
```

## Building

### Linux/WSL Build

```bash
cd verilator/
./verilate_gameboy.sh
```

### Running (CLI Version - Linux/WSL)

```bash
# Run with a specific ROM file
cd verilator
./obj_dir/Vtop /path/to/game.gb

# Or place a ROM in the working directory
cp /path/to/game.gb verilator/game.gb
./obj_dir/Vtop

# Run with VCD trace output
./obj_dir/Vtop game.gb --trace trace.vcd --frames 100

# Run headless (automated testing)
./obj_dir/Vtop game.gb --frames 60
```

### Running (GUI Version - Visual Studio/Windows)

The GUI version (`sim_main_gui.cpp`) requires ImGui and SDL. Build with Visual Studio:

1. Open the Visual Studio solution in `verilator/`
2. Build the project (requires SDL2 and ImGui libraries)
3. Run and load ROMs through the GUI

## Simulation Versions

| File | Description | Platform |
|------|-------------|----------|
| `sim_main.cpp` | CLI with VCD tracing | Linux/WSL |
| `sim_main_gui.cpp` | ImGui GUI | Windows/VS |
| `sim_main_headless.cpp` | Automated testing | CI/CD |

## Simulator Controls (Keyboard)

| Key | Function |
|-----|----------|
| Arrow Keys | D-Pad |
| Z | A Button |
| X | B Button |
| Enter | Start |
| Right Shift | Select |

Additional controls:
- Simulation control panel: Start/Stop/Reset, step through cycles
- VCD tracing: Enable/disable waveform capture
- SDRAM Status: View read/write counts, row hit rate

## Current Status

- **CPU**: TV80 with Game Boy mode (Mode=3) - *Fully integrated*
- **Video**: LCD output (160x144) - *Working*
- **Audio**: Sound chip - *Stubbed (silent)*
- **SDRAM**: 32MB C++ model - *Fully functional*
- **Cartridge**: Full MBC support via SDRAM - *All mappers supported*
- **Savestates**: *Disabled*

## Supported Mappers

- MBC1, MBC1M (multicart)
- MBC2
- MBC3 (with RTC stub)
- MBC5
- MBC6, MBC7
- MMM01
- HuC1, HuC3
- GB Camera
- TAMA5
- Sachen
- Wisdom Tree
- Megaduck

## SDRAM Architecture

The simulator uses a C++ SDRAM model that accurately emulates:
- Native SDRAM command interface (ACT, READ, WRITE, PRE, REF, MRS)
- CAS latency timing
- Bank/row/column addressing
- Byte enables

ROM data is loaded directly into the SDRAM model at startup, and the MiSTer SDRAM controller (sdram.sv) handles all memory access timing.

## Known Limitations

1. **Sound disabled** - gbc_snd is stubbed, producing no audio
2. **No savestates** - Savestate functionality is stubbed
3. **RTC stub** - MBC3 RTC returns fixed time
4. **No backup RAM persistence** - Cart RAM not saved to disk

## Signal Inspection

You can inspect RTL signals in two ways:
- VCD tracing: enable VCD export from the Trace window in the simulator UI
- Live ImGui panel: read public signals via `top->rootp->...`

To expose internal nets, mark them `/*verilator public*/` in the RTL and rerun the build script.

## Credits

- **GameBoy MiSTer Core**: [MiSTer-devel](https://github.com/MiSTer-devel/Gameboy_MiSTer)
- **TV80 Z80 Core**: [hutch31/tv80](https://github.com/hutch31/tv80)
- **Original T80 Core**: Daniel Wallner
- **Verilator Template**: Based on Arcade-Centipede simulation framework

## License

- TV80: MIT License
- GameBoy MiSTer Core: GNU General Public License v3
- Simulation Framework: As per original template
