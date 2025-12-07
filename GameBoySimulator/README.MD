# GameBoy Verilator Simulator

A Verilator-based simulation of the GameBoy MiSTer core with the TV80 Verilog CPU replacing the original VHDL T80 CPU.

## Overview

This simulator combines:
- **GameBoy MiSTer Core** - Full GameBoy/GameBoy Color emulation from [MiSTer-devel/Gameboy_MiSTer](https://github.com/MiSTer-devel/Gameboy_MiSTer)
- **TV80 Z80 CPU** - Verilog implementation from [hutch31/tv80](https://github.com/hutch31/tv80)
- **Verilator Simulation Framework** - ImGui-based interactive GUI

## Key Changes from Original

The original GameBoy MiSTer core uses T80 (VHDL). This version:
1. Replaces T80 with TV80 (Verilog) using Game Boy mode (Mode=3)
2. Provides Verilog stubs for VHDL modules (dpram, gbc_snd, savestates)
3. Enables full Verilator simulation without VHDL dependencies

## Directory Structure

```
GameBoySimulator/
├── gameboy_core/       # Cloned GameBoy MiSTer core
│   └── rtl/            # Original RTL files
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
├── verilator/          # Simulation files
│   ├── gameboy_sim.v   # Top-level wrapper
│   ├── sim_main.cpp    # C++ simulation main
│   ├── verilate_gameboy.sh  # Build script
│   └── sim/            # ImGui and simulation support
└── sim/                # C++ simulation models
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

### Running

```bash
# Place a GameBoy ROM in the verilator working directory
cp /path/to/game.gb verilator/game.gb

# Run the simulator
cd verilator
./obj_dir/Vtop
```

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

## Current Status

- **CPU**: TV80 with Game Boy mode (Mode=3) - *Integrated*
- **Video**: LCD output (160x144) - *Basic support*
- **Audio**: Sound chip - *Stubbed (silent)*
- **Savestates**: *Disabled*
- **Cartridge**: Simple 32KB ROM - *Basic support*

## Known Limitations

1. **Sound disabled** - gbc_snd is stubbed, producing no audio
2. **Limited MBC support** - Complex mappers may not work
3. **No savestates** - Savestate functionality is stubbed
4. **DMG mode only** - Running in original GameBoy mode

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
