# Verilator Linting Setup for PCXT Project

This directory contains configuration files for running Verilator lint checks on the PCXT hardware design.

## Installation

To install Verilator on Ubuntu/Debian:

```bash
sudo apt-get update
sudo apt-get install verilator
```

## Files Created

- `build_id.v` - Build ID stub for compilation
- `verilator.vlt` - Verilator lint configuration (waiver file)
- `verilator_files.f` - List of all source files
- `run_verilator_lint.sh` - Shell script to run Verilator lint
- `stubs/` - Directory containing stubs for Altera/MiSTer-specific modules:
  - `hps_io.sv` - MiSTer HPS I/O interface stub
  - `pll.v` - Main PLL stub
  - `pllsdram.v` - SDRAM PLL stub

## Running Verilator Lint

### Quick Method

Simply run the provided script:

```bash
cd /home/user/MyPC/Quartus
./run_verilator_lint.sh
```

The results will be saved to `verilator_lint.log`.

### Manual Method

For more control, you can run Verilator directly:

```bash
cd /home/user/MyPC/Quartus

verilator --lint-only \
    -Wall \
    -Wno-fatal \
    -sv \
    --top-module emu \
    -I. -Istubs -Irtl \
    mycore.sv \
    [other source files...]
```

## Understanding the Output

Verilator will report various warnings and errors:

- **Errors**: Must be fixed - these indicate serious design issues
- **Warnings**: Should be reviewed - may indicate potential problems
  - `UNUSED`: Signals that are declared but never used
  - `UNDRIVEN`: Signals that are never assigned a value
  - `WIDTH`: Bit width mismatches
  - `LATCH`: Unintended latches (incomplete assignments)

## Common Issues

### Altera/Intel-Specific Modules

The design uses Altera/Intel FPGA-specific IP cores (PLLs, etc.). These have been stubbed out in the `stubs/` directory for linting purposes. The actual hardware implementation uses the generated IP cores.

### MiSTer Framework

This project uses the MiSTer FPGA framework. Some MiSTer-specific modules (like `hps_io`) have been stubbed for linting.

## Focusing on Custom Logic

To focus lint checks on your custom RTL and ignore stubbed modules, you can modify `verilator.vlt` to add more lint waivers.

## Integration with CI/CD

You can integrate this into your CI/CD pipeline:

```bash
./run_verilator_lint.sh
if grep -q "Error:" verilator_lint.log; then
    echo "Verilator found errors!"
    exit 1
fi
```

## Notes

- The `build_id.v` file is normally auto-generated during Quartus synthesis. A stub version has been created for linting.
- Some warnings are expected due to the nature of FPGA designs (e.g., asynchronous resets, vendor IP)
- Focus on fixing warnings in your custom RTL code (CPU, peripherals, etc.)
